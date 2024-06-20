/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsmtutil/SMTLib2Interface.h>

#include <libsolutil/Keccak256.h>

#include <boost/algorithm/string/join.hpp>
#include <boost/algorithm/string/predicate.hpp>

#include <range/v3/algorithm/find_if.hpp>

#include <array>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>

using namespace solidity;
using namespace solidity::util;
using namespace solidity::frontend;
using namespace solidity::smtutil;

SMTLib2Interface::SMTLib2Interface(
	std::map<h256, std::string> _queryResponses,
	ReadCallback::Callback _smtCallback,
	std::optional<unsigned> _queryTimeout
):
	SolverInterface(_queryTimeout),
	m_queryResponses(std::move(_queryResponses)),
	m_smtCallback(std::move(_smtCallback))
{
	reset();
}

void SMTLib2Interface::reset()
{
	m_commands.clear();
	m_variables.clear();
	m_userSorts.clear();
	m_sortNames.clear();
	m_commands.setOption("produce-models", "true");
	if (m_queryTimeout)
		m_commands.setOption("timeout", std::to_string(*m_queryTimeout));
	m_commands.setLogic("ALL");
}

void SMTLib2Interface::push()
{
	m_commands.push();
}

void SMTLib2Interface::pop()
{
	m_commands.pop();
}

void SMTLib2Interface::declareVariable(std::string const& _name, SortPointer const& _sort)
{
	smtAssert(_sort, "");
	if (_sort->kind == Kind::Function)
		declareFunction(_name, _sort);
	else if (!m_variables.count(_name))
	{
		m_variables.emplace(_name, _sort);
		m_commands.declareVariable(_name, toSmtLibSort(_sort));
	}
}

void SMTLib2Interface::declareFunction(std::string const& _name, SortPointer const& _sort)
{
	smtAssert(_sort, "");
	smtAssert(_sort->kind == Kind::Function, "");
	// TODO Use domain and codomain as key as well
	if (!m_variables.count(_name))
	{
		auto const& fSort = std::dynamic_pointer_cast<FunctionSort>(_sort);
		auto domain = toSmtLibSort(fSort->domain);
		std::string codomain = toSmtLibSort(fSort->codomain);
		m_variables.emplace(_name, _sort);
		m_commands.declareFunction(_name, domain, codomain);
	}
}

void SMTLib2Interface::addAssertion(Expression const& _expr)
{
	m_commands.assertion(toSExpr(_expr));
}

std::pair<CheckResult, std::vector<std::string>> SMTLib2Interface::check(std::vector<Expression> const& _expressionsToEvaluate)
{
	std::cout << dumpQuery({}) << std::endl;
	std::string response = querySolver(dumpQuery(_expressionsToEvaluate));

	CheckResult result;
	// TODO proper parsing
	if (boost::starts_with(response, "sat"))
		result = CheckResult::SATISFIABLE;
	else if (boost::starts_with(response, "unsat"))
		result = CheckResult::UNSATISFIABLE;
	else if (boost::starts_with(response, "unknown"))
		result = CheckResult::UNKNOWN;
	else
		result = CheckResult::ERROR;

	std::vector<std::string> values;
	if (result == CheckResult::SATISFIABLE && !_expressionsToEvaluate.empty())
		values = parseValues(find(response.cbegin(), response.cend(), '\n'), response.cend());
	return std::make_pair(result, values);
}

std::string SMTLib2Interface::toSExpr(Expression const& _expr)
{
	if (_expr.arguments.empty())
		return _expr.name;

	std::string sexpr = "(";
	if (_expr.name == "int2bv")
	{
		size_t size = std::stoul(_expr.arguments[1].name);
		auto arg = toSExpr(_expr.arguments.front());
		auto int2bv = "(_ int2bv " + std::to_string(size) + ")";
		// Some solvers treat all BVs as unsigned, so we need to manually apply 2's complement if needed.
		sexpr += std::string("ite ") +
			"(>= " + arg + " 0) " +
			"(" + int2bv + " " + arg + ") " +
			"(bvneg (" + int2bv + " (- " + arg + ")))";
	}
	else if (_expr.name == "bv2int")
	{
		auto intSort = std::dynamic_pointer_cast<IntSort>(_expr.sort);
		smtAssert(intSort, "");

		auto arg = toSExpr(_expr.arguments.front());
		auto nat = "(bv2nat " + arg + ")";

		if (!intSort->isSigned)
			return nat;

		auto bvSort = std::dynamic_pointer_cast<BitVectorSort>(_expr.arguments.front().sort);
		smtAssert(bvSort, "");
		auto size = std::to_string(bvSort->size);
		auto pos = std::to_string(bvSort->size - 1);

		// Some solvers treat all BVs as unsigned, so we need to manually apply 2's complement if needed.
		sexpr += std::string("ite ") +
			"(= ((_ extract " + pos + " " + pos + ")" + arg + ") #b0) " +
			nat + " " +
			"(- (bv2nat (bvneg " + arg + ")))";
	}
	else if (_expr.name == "const_array")
	{
		smtAssert(_expr.arguments.size() == 2, "");
		auto sortSort = std::dynamic_pointer_cast<SortSort>(_expr.arguments.at(0).sort);
		smtAssert(sortSort, "");
		auto arraySort = std::dynamic_pointer_cast<ArraySort>(sortSort->inner);
		smtAssert(arraySort, "");
		sexpr += "(as const " + toSmtLibSort(arraySort) + ") ";
		sexpr += toSExpr(_expr.arguments.at(1));
	}
	else if (_expr.name == "tuple_get")
	{
		smtAssert(_expr.arguments.size() == 2, "");
		auto tupleSort = std::dynamic_pointer_cast<TupleSort>(_expr.arguments.at(0).sort);
		size_t index = std::stoul(_expr.arguments.at(1).name);
		smtAssert(index < tupleSort->members.size(), "");
		sexpr += "|" + tupleSort->members.at(index) + "| " + toSExpr(_expr.arguments.at(0));
	}
	else if (_expr.name == "tuple_constructor")
	{
		auto tupleSort = std::dynamic_pointer_cast<TupleSort>(_expr.sort);
		smtAssert(tupleSort, "");
		sexpr += "|" + tupleSort->name + "|";
		for (auto const& arg: _expr.arguments)
			sexpr += " " + toSExpr(arg);
	}
	else
	{
		sexpr += _expr.name;
		for (auto const& arg: _expr.arguments)
			sexpr += " " + toSExpr(arg);
	}
	sexpr += ")";
	return sexpr;
}

std::string SMTLib2Interface::toSmtLibSort(SortPointer _sort)
{
	if (!m_sortNames.count(_sort))
		m_sortNames[_sort] = toSmtLibSortInternal(_sort);
	return m_sortNames.at(_sort);
}

std::string SMTLib2Interface::toSmtLibSortInternal(SortPointer _sort)
{
	switch (_sort->kind)
	{
	case Kind::Int:
		return "Int";
	case Kind::Bool:
		return "Bool";
	case Kind::BitVector:
		return "(_ BitVec " + std::to_string(dynamic_cast<BitVectorSort const&>(*_sort).size) + ")";
	case Kind::Array:
	{
		auto const& arraySort = dynamic_cast<ArraySort const&>(*_sort);
		smtAssert(arraySort.domain && arraySort.range, "");
		return "(Array " + toSmtLibSort(arraySort.domain) + ' ' + toSmtLibSort(arraySort.range) + ')';
	}
	case Kind::Tuple:
	{
		auto const& tupleSort = dynamic_cast<TupleSort const&>(*_sort);
		std::string const& tupleName = tupleSort.name;
		auto isName = [&](auto entry) { return entry.first == tupleName; };
		if (ranges::find_if(m_userSorts, isName) == m_userSorts.end())
		{
			smtAssert(tupleSort.members.size() == tupleSort.components.size());
			auto declaration = m_commands.declareTuple(tupleName, tupleSort.members, toSmtLibSort(tupleSort.components));
			m_userSorts.emplace_back(tupleName, std::move(declaration));
		}

		return tupleName;
	}
	default:
		smtAssert(false, "Invalid SMT sort");
	}
}

std::vector<std::string> SMTLib2Interface::toSmtLibSort(std::vector<SortPointer> const& _sorts)
{
	std::vector<std::string> ssorts;
	ssorts.reserve(_sorts.size());
	for (auto const& sort: _sorts)
		ssorts.push_back(toSmtLibSort(sort));
	return ssorts;
}

std::string SMTLib2Interface::checkSatAndGetValuesCommand(std::vector<Expression> const& _expressionsToEvaluate)
{
	std::string command;
	if (_expressionsToEvaluate.empty())
		command = "(check-sat)\n";
	else
	{
		// TODO make sure these are unique
		for (size_t i = 0; i < _expressionsToEvaluate.size(); i++)
		{
			auto const& e = _expressionsToEvaluate.at(i);
			smtAssert(e.sort->kind == Kind::Int || e.sort->kind == Kind::Bool, "Invalid sort for expression to evaluate.");
			command += "(declare-const |EVALEXPR_" + std::to_string(i) + "| " + (e.sort->kind == Kind::Int ? "Int" : "Bool") + ")\n";
			command += "(assert (= |EVALEXPR_" + std::to_string(i) + "| " + toSExpr(e) + "))\n";
		}
		command += "(check-sat)\n";
		command += "(get-value (";
		for (size_t i = 0; i < _expressionsToEvaluate.size(); i++)
			command += "|EVALEXPR_" + std::to_string(i) + "| ";
		command += "))\n";
	}

	return command;
}

std::vector<std::string> SMTLib2Interface::parseValues(std::string::const_iterator _start, std::string::const_iterator _end)
{
	std::vector<std::string> values;
	while (_start < _end)
	{
		auto valStart = find(_start, _end, ' ');
		if (valStart < _end)
			++valStart;
		auto valEnd = find(valStart, _end, ')');
		values.emplace_back(valStart, valEnd);
		_start = find(valEnd, _end, '(');
	}

	return values;
}

std::string SMTLib2Interface::querySolver(std::string const& _input)
{
	h256 inputHash = keccak256(_input);
	if (m_queryResponses.count(inputHash))
		return m_queryResponses.at(inputHash);
	if (m_smtCallback)
	{
		setupSmtCallback();
		auto result = m_smtCallback(ReadCallback::kindString(ReadCallback::Kind::SMTQuery), _input);
		if (result.success)
			return result.responseOrErrorMessage;
	}
	m_unhandledQueries.push_back(_input);
	return "unknown\n";
}

std::string SMTLib2Interface::dumpQuery(std::vector<Expression> const& _expressionsToEvaluate)
{
	return m_commands.toString() + checkSatAndGetValuesCommand(_expressionsToEvaluate);
}


void SMTLib2Commands::push() {
	m_frameLimits.push_back(m_commands.size());
}

void SMTLib2Commands::pop() {
	smtAssert(!m_commands.empty());
	auto limit = m_frameLimits.back();
	m_frameLimits.pop_back();
	while (m_commands.size() > limit)
		m_commands.pop_back();
}

std::string SMTLib2Commands::toString() const {
	return boost::algorithm::join(m_commands, "\n");
}

void SMTLib2Commands::clear() {
	m_commands.clear();
	m_frameLimits.clear();
}

void SMTLib2Commands::assertion(std::string _expr) {
	m_commands.push_back("(assert " + std::move(_expr) + ')');
}

void SMTLib2Commands::setOption(std::string _name, std::string _value)
{
	m_commands.push_back("(set-option :" + std::move(_name) + ' ' + std::move(_value) + ')');
}

void SMTLib2Commands::setLogic(std::string _logic)
{
	m_commands.push_back("(set-logic " + std::move(_logic) + ')');
}

void SMTLib2Commands::declareVariable(std::string _name, std::string _sort)
{
		m_commands.push_back("(declare-fun |" + std::move(_name) + "| () " + std::move(_sort) + ')');
}

void SMTLib2Commands::declareFunction(std::string const& _name, std::vector<std::string> const& _domain, std::string const& _codomain)
{
	std::stringstream ss;
	ss << "(declare-fun |" << _name << "| " << '(';
	for (auto && arg : _domain)
		ss << arg;
	ss << ')' << ' ' << _codomain << ')';
	m_commands.push_back(ss.str());
}

std::string SMTLib2Commands::declareTuple(
	std::string const& _name,
	std::vector<std::string> const& _memberNames,
	std::vector<std::string> const& _memberSorts
)
{
	auto quotedName = '|' + _name + '|';
	std::stringstream ss;
	ss << "(declare-datatypes ((" << quotedName << " 0)) (((" << quotedName;
	for (auto && [memberName, memberSort]: ranges::views::zip(_memberNames, _memberSorts))
		ss << " (|" << memberName << "| " << memberSort << ")";
	ss << "))))";
	auto declaration = ss.str();
	m_commands.push_back(ss.str());
	return declaration;
}
