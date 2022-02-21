define _jump-fcontext
  dont-repeat
  if $argc < 1
    echo Error, jump-fcontext requires an fcontext_t as an argument\n
  else
    set $fctx = 0
    set $fctx = (void*)($arg0)
    if $fctx != 0
      select-frame 0
      set $out = malloc(0x4c)

      set *(int*)($out + 0x0) = (int)$mxcsr
      set *(short*)($out + 0x4) = (short)$fctrl
      set *(long*)($out + 0x8) = $r12
      set *(long*)($out + 0x10) = $r13
      set *(long*)($out + 0x18) = $r14
      set *(long*)($out + 0x20) = $r15
      set *(long*)($out + 0x28) = $rbx
      set *(long*)($out + 0x30) = $rbp
      set *(long*)($out + 0x38) = $rip
      set *(long*)($out + 0x40) = $rsp
      set *(char[4]*)($out + 0x48) = "GDB"
      print $out

      set $mxcsr = *(int*)($fctx + 0x0)
      set $fctrl = *(char*)($fctx + 0x4)
      set $r12 = *(long*)($fctx + 0x8)
      set $r13 = *(long*)($fctx + 0x10)
      set $r14 = *(long*)($fctx + 0x18)
      set $r15 = *(long*)($fctx + 0x20)
      set $rbx = *(long*)($fctx + 0x28)
      set $strid = (char*)($fctx + 0x48)
      set $rip = *(long*)($fctx + 0x38)
      set $rsp = *(long*)($fctx + 0x40)
      # I get issues if I try to assign $rbp before $rsp
      set $rbp = *(long*)($fctx + 0x30)
      # I have no idea why this is necessary, but it is
      set $rip = *(long*)($fctx + 0x38)
      if $strid[0] == 'G' && $strid[1] == 'D' && $strid[2] == 'B'
        call free($fctx)
      end

      #frame
    end
  end
end

define jump-fcontext
  dont-repeat
  _jump-fcontext ($arg0)
  frame
end

define jump-coroutine
  dont-repeat
  if $argc < 1
    echo Error, jump-coroutine requires a coroutine as an argument\n
  else
    _jump-fcontext ($arg0).cb_.c.fctx_
    frame 3
  end
end

#define return_fcontext
#  if $argc < 1
#    echo Error, return_fcontext requires the output of jump_fcontext as argument
#  else
#    set $mxcsr = $arg0[0]
#    set $fctrl = $arg0[1]
#    set $r12 = $arg0[2]
#    set $r13 = $arg0[3]
#    set $r14 = $arg0[4]
#    set $r15 = $arg0[5]
#    srg $rbx = $arg0[6]
#    set $rbp = $arg0[7]
#    set $rsp = $arg0[8]
#    set $rip = $arg0[9]
#    frame
#  end
#end
