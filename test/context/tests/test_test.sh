
# Test the testing framework itself
addtest "$(trcmd exit 4)" "exit 4" 4 1
addtest "$(trcmd exit 0)" "exit 0" 0 1
