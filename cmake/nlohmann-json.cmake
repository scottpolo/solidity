add_library(nlohmann-json INTERFACE IMPORTED)
file(MAKE_DIRECTORY ${CMAKE_SOURCE_DIR}/deps/json)
set_target_properties(nlohmann-json PROPERTIES
        INTERFACE_COMPILE_OPTIONS "\$<\$<CXX_COMPILER_ID:MSVC>:/permissive->"
        INTERFACE_SYSTEM_INCLUDE_DIRECTORIES  ${CMAKE_SOURCE_DIR}/deps/json/include
        INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_SOURCE_DIR}/deps/json/include)
add_dependencies(nlohmann-json nlohmann-json-project)
