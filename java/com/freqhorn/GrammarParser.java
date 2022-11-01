package com.freqhorn;

import com.freqhorn.Grammar;

import java.io.File;

public abstract class GrammarParser {
  public static native Grammar ParseFromString(String s, String programFilename);
  public static native Grammar ParseFromFile(String filename, String programFilename);
  static {
    System.loadLibrary("jfreqhorn");
  }
}
