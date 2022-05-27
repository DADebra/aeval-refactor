target_include_directories(global PUBLIC ./include)
target_include_directories(global PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/include)
add_subdirectory(tools)
add_subdirectory(include)
