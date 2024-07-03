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

#include <libsolidity/formal/Z3CHCSmtLib2Interface.h>

#include <libsolidity/interface/UniversalCallback.h>

#include <libsmtutil/SMTLib2Parser.h>

#include <boost/algorithm/string/predicate.hpp>

#include <stack>

using namespace solidity::frontend::smt;
using namespace solidity::smtutil;

Z3CHCSmtLib2Interface::Z3CHCSmtLib2Interface(
	frontend::ReadCallback::Callback _smtCallback,
	std::optional<unsigned int> _queryTimeout
): CHCSmtLib2Interface({}, std::move(_smtCallback), _queryTimeout)
{
}

void Z3CHCSmtLib2Interface::setupSmtCallback(bool _enablePreprocessing)
{
	if (auto* universalCallback = m_smtCallback.target<frontend::UniversalCallback>())
		universalCallback->smtCommand().setZ3(m_queryTimeout, _enablePreprocessing);
}

std::tuple<CheckResult, Expression, CHCSolverInterface::CexGraph> Z3CHCSmtLib2Interface::query(smtutil::Expression const& _block)
{
	setupSmtCallback(true);
	std::string query = dumpQuery(_block);
	std::string response = querySolver(query);
	if (boost::starts_with(response, "unsat"))
	{
		// Repeat the query with preprocessing disabled, to get the full proof
		setupSmtCallback(false);
		query = "(set-option :produce-proofs true)" + query + "\n(get-proof)";
		response = querySolver(query);
		setupSmtCallback(true);
		if (!boost::starts_with(response, "unsat"))
			return {CheckResult::SATISFIABLE, Expression(true), {}};
		return {CheckResult::SATISFIABLE, Expression(true), graphFromZ3Answer(response)};
	}

	CheckResult result;
	if (boost::starts_with(response, "sat"))
	{
		auto maybeInvariants = invariantsFromSolverResponse(response);
		return {CheckResult::UNSATISFIABLE, maybeInvariants.value_or(Expression(true)), {}};
	}
	else if (boost::starts_with(response, "unknown"))
		result = CheckResult::UNKNOWN;
	else
		result = CheckResult::ERROR;

	return {result, Expression(true), {}};
}

namespace
{

struct LetBindings
{
	using BindingRecord = std::vector<SMTLib2Expression>;
	std::unordered_map<std::string, BindingRecord> bindings;
	std::vector<std::string> varNames;
	std::vector<std::size_t> scopeBounds;

	bool has(std::string const& varName) { return bindings.find(varName) != bindings.end(); }

	SMTLib2Expression& operator[](std::string const& varName)
	{
		auto it = bindings.find(varName);
		solAssert(it != bindings.end());
		solAssert(!it->second.empty());
		return it->second.back();
	}

	void pushScope() { scopeBounds.push_back(varNames.size()); }

	void popScope()
	{
		smtAssert(!scopeBounds.empty());
		auto bound = scopeBounds.back();
		while (varNames.size() > bound)
		{
			auto const& varName = varNames.back();
			auto it = bindings.find(varName);
			smtAssert(it != bindings.end());
			auto& record = it->second;
			record.pop_back();
			if (record.empty())
				bindings.erase(it);
			varNames.pop_back();
		}
		scopeBounds.pop_back();
	}

	void addBinding(std::string name, SMTLib2Expression expression)
	{
		auto it = bindings.find(name);
		if (it == bindings.end())
			bindings.insert({name, {std::move(expression)}});
		else
			it->second.push_back(std::move(expression));
		varNames.push_back(std::move(name));
	}
};

void inlineLetExpressions(SMTLib2Expression& _expr, LetBindings & _bindings)
	{
		if (isAtom(_expr))
		{
			auto const& atom = asAtom(_expr);
			if (_bindings.has(atom))
				_expr = _bindings[atom];
			return;
		}
		auto& subexprs = asSubExpressions(_expr);
		solAssert(!subexprs.empty());
		auto const& first = subexprs.at(0);
		if (isAtom(first) && asAtom(first) == "let")
		{
			solAssert(subexprs.size() >= 3);
			solAssert(!isAtom(subexprs[1]));
			auto& bindingExpressions = asSubExpressions(subexprs[1]);
			// process new bindings
			std::vector<std::pair<std::string, SMTLib2Expression>> newBindings;
			for (auto& binding: bindingExpressions)
			{
				solAssert(!isAtom(binding));
				auto& bindingPair = asSubExpressions(binding);
				solAssert(bindingPair.size() == 2);
				solAssert(isAtom(bindingPair.at(0)));
				inlineLetExpressions(bindingPair.at(1), _bindings);
				newBindings.emplace_back(asAtom(bindingPair.at(0)), bindingPair.at(1));
			}
			_bindings.pushScope();
			for (auto&& [name, expr]: newBindings)
				_bindings.addBinding(std::move(name), std::move(expr));
			newBindings.clear();

			// get new subexpression
			inlineLetExpressions(subexprs.at(2), _bindings);
			// remove the new bindings
			_bindings.popScope();

			// update the expression
			auto tmp = std::move(subexprs.at(2));
			_expr = std::move(tmp);
			return;
		}
		// not a let expression, just process all arguments
		for (auto& subexpr: subexprs)
		{
			inlineLetExpressions(subexpr, _bindings);
		}
	}

	void inlineLetExpressions(SMTLib2Expression& expr)
	{
		LetBindings bindings;
		inlineLetExpressions(expr, bindings);
	}
}


CHCSolverInterface::CexGraph Z3CHCSmtLib2Interface::graphFromZ3Answer(std::string const& _proof) const
{
	std::stringstream ss(_proof);
	std::string answer;
	ss >> answer;
	smtAssert(answer == "unsat");

	SMTLib2Parser parser(ss);
	if (parser.isEOF()) // No proof from Z3
		return {};
	// For some reason Z3 outputs everything as a single s-expression
	SMTLib2Expression parsedOutput;
	try
	{
		parsedOutput = parser.parseExpression();
	}
	catch (SMTLib2Parser::ParsingException&)
	{
		return {};
	}
	solAssert(parser.isEOF());
	solAssert(!isAtom(parsedOutput));
	auto& commands = asSubExpressions(parsedOutput);
	ScopedParser expressionParser(m_context);
	for (auto& command: commands)
	{
		if (isAtom(command))
			continue;

		auto const& args = asSubExpressions(command);
		auto const& head = args[0];
		if (!isAtom(head))
			continue;

		if (asAtom(head) == "declare-fun")
		{
			solAssert(args.size() == 4);
			auto const& name = args[1];
			auto const& domainSorts = args[2];
			auto const& codomainSort = args[3];
			solAssert(isAtom(name));
			solAssert(!isAtom(domainSorts));
			expressionParser.addVariableDeclaration(asAtom(name), expressionParser.toSort(codomainSort));
		}
		else if (asAtom(head) == "proof")
		{
			inlineLetExpressions(command);
			return graphFromSMTLib2Expression(command, expressionParser);
		}
	}
	return {};
}

CHCSolverInterface::CexGraph Z3CHCSmtLib2Interface::graphFromSMTLib2Expression(
	SMTLib2Expression const& _proof,
	ScopedParser& context
)
{
	auto fact = [](SMTLib2Expression const& _node) -> SMTLib2Expression const& {
		if (isAtom(_node))
			return _node;
		smtAssert(!asSubExpressions(_node).empty());
		return asSubExpressions(_node).back();
	};
	smtAssert(!isAtom(_proof));
	auto const& proofArgs = asSubExpressions(_proof);
	smtAssert(proofArgs.size() == 2);
	smtAssert(isAtom(proofArgs.at(0)) && asAtom(proofArgs.at(0)) == "proof");
	auto const& proofNode = proofArgs.at(1);
	auto const& derivedFact = fact(proofNode);
	if (isAtom(proofNode) || !isAtom(derivedFact) || asAtom(derivedFact) != "false")
		return {};

	CHCSolverInterface::CexGraph graph;

	std::stack<SMTLib2Expression const*> proofStack;
	proofStack.push(&asSubExpressions(proofNode).at(1));

	std::map<SMTLib2Expression const*, unsigned> visitedIds;
	unsigned nextId = 0;

	auto const* root = proofStack.top();
	auto const& derivedRootFact = fact(*root);
	visitedIds.insert({root, nextId++});
	graph.nodes.emplace(visitedIds.at(root), context.toSMTUtilExpression(derivedRootFact));

	auto isHyperRes = [](SMTLib2Expression const& expr) {
		if (isAtom(expr)) return false;
		auto const& subExprs = asSubExpressions(expr);
		smtAssert(!subExprs.empty());
		auto const& op = subExprs.at(0);
		if (isAtom(op)) return false;
		auto const& opExprs = asSubExpressions(op);
		if (opExprs.size() < 2) return false;
		auto const& ruleName = opExprs.at(1);
		return isAtom(ruleName) && asAtom(ruleName) == "hyper-res";
	};

	while (!proofStack.empty())
	{
		auto const* currentNode = proofStack.top();
		smtAssert(visitedIds.find(currentNode) != visitedIds.end());
		auto id = visitedIds.at(currentNode);
		smtAssert(graph.nodes.count(id));
		proofStack.pop();

		if (isHyperRes(*currentNode))
		{
			auto const& args = asSubExpressions(*currentNode);
			smtAssert(args.size() > 1);
			// args[0] is the name of the rule
			// args[1] is the clause used
			// last argument is the derived fact
			// the arguments in the middle are the facts where we need to recurse
			for (unsigned i = 2; i < args.size() - 1; ++i)
			{
				auto const* child = &args[i];
				if (!visitedIds.count(child))
				{
					visitedIds.insert({child, nextId++});
					proofStack.push(child);
				}

				auto childId = visitedIds.at(child);
				if (!graph.nodes.count(childId))
				{
					graph.nodes.emplace(childId, context.toSMTUtilExpression(fact(*child)));
					graph.edges[childId] = {};
				}

				graph.edges[id].push_back(childId);
			}
		}
	}
	return graph;
}

