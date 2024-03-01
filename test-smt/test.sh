#!/bin/sh
# Shell script to test some verification examples

# Check differences:
check_diff() {
  OUTFILE=$1
  RESULTFILE=$2
  DIFF=diff$$
  diff $RESULTFILE $OUTFILE > $DIFF
  if [ "`cat $DIFF`" = "" ] ; then
    echo
    echo "Regression test successfully executed!"
    /bin/rm -f $OUTFILE $DIFF
  else
    echo
    echo "Differences in regression test occurred:"
    cat $DIFF
    /bin/rm -f $DIFF
    /bin/mv -f $OUTFILE LOGFILE
    echo "Test output saved in file 'LOGFILE'."
    exit 1
  fi
}

LOGFILE=xxx$$
# Example programs to be tested:
TESTPROGS="Fac UseFac FacMore FacIO UseDiv Diamond Sig ListLength Nth NthInfer NthZero NthZeroNonFail NthZeroNonFailWrong One HeadPos CharBounds"

# Testing standard (top constructor) domain:
TOOL="curry-calltypes"

$TOOL -r -q $TESTPROGS 2>&1 | tee $LOGFILE
check_diff $LOGFILE RESULTEXAMPLES.txt
