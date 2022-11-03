package com.freqhorn;

import com.freqhorn.Grammar;

import java.io.File;

/** Static class which provides methods for parsing a grammar into a
 * Java-native format.
 */
public final class GrammarParser {
  /** Parse the grammar from the contents of the given string, returning a
   * {@link Grammar} object.
   * <p>
   * The string must be in the same on-file format, i.e. you could read the
   * full file into a String and send it to this method.
   * <p>
   * {@code} programFilename is the path of the program being proven,
   * needed to fill certain variables in the grammar.
   */
  public static native Grammar ParseFromString(String s, String programFilename);

  /** Parse the grammar from the contents of the given file path, returning a
   * {@link Grammar} object.
   * <p>
   * {@code} programFilename is the path of the program being proven,
   * needed to fill certain variables in the grammar.
   */
  public static native Grammar ParseFromFile(String filename, String programFilename);
  static {
    System.loadLibrary("jfreqhorn");
  }
}
