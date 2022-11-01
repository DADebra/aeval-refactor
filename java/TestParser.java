
import com.freqhorn.Grammar;
import com.freqhorn.GrammarParser;
import com.freqhorn.Expr;
import com.freqhorn.ExprSorts;

public class TestParser {
  public static void main(String[] args) {
    if (args.length < 2) {
      System.out.println("Usage: TestParser grammar_file.smt2 program.smt2");
      return;
    }
    Expr teste = ExprSorts.Int;
    Grammar gram = GrammarParser.ParseFromFile(args[0], args[1]);
    System.out.println("Grammar:\n" + gram.toString());
  }
}
