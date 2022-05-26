add_executable (expl BoundedExplorer.cpp)
target_link_libraries(expl global)
target_link_libraries (expl ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS expl RUNTIME DESTINATION bin)

add_executable (freqhorn DeepHorn.cpp)
target_link_libraries(freqhorn global)
target_link_libraries (freqhorn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS freqhorn RUNTIME DESTINATION bin)

#add_executable (kind KInduction.cpp)
#target_link_libraries (kind ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
#install(TARGETS kind RUNTIME DESTINATION bin)
