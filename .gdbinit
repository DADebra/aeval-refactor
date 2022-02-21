define printexpr
  if $argc < 1
    echo Error, printexpr requires an Expr as an argument\n
  else
    p ($arg0)->Print(std::cerr, 0, false)
  end
end

alias -a pe = printexpr
source jump_fcontext.gdb
