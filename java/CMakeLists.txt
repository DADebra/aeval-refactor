find_package(Java 1.8 COMPONENTS Development)
if (Java_FOUND)
  include(UseJava)
  set(JAVA_SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/com/freqhorn)
  add_jar(jfreqhorn
    SOURCES
      ${JAVA_SOURCE_DIR}/GrammarParser.java
      ${JAVA_SOURCE_DIR}/Grammar.java
      ${JAVA_SOURCE_DIR}/Expr.java
      ${JAVA_SOURCE_DIR}/ExprVal.java
      ${JAVA_SOURCE_DIR}/ExprIntVal.java
      ${JAVA_SOURCE_DIR}/ExprRealVal.java
      ${JAVA_SOURCE_DIR}/ExprBoolVal.java
      ${JAVA_SOURCE_DIR}/ExprStringVal.java
      ${JAVA_SOURCE_DIR}/ExprOp.java
      ${JAVA_SOURCE_DIR}/ExprSorts.java
    GENERATE_NATIVE_HEADERS jfreqhorn-native)
  add_jar(testparser
    SOURCES TestParser.java
    INCLUDE_JARS jfreqhorn
    MANIFEST TestParser.MF
    ENTRY_POINT TestParser)
endif()
