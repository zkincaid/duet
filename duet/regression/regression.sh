#!/bin/bash

# Run a set of regression tests.
# Command line arguments
#   run              Run the suite of regression tests
#   run <set>        Run a particular set of regression tests
#   baselines        Generate baselines for all regression tests
#   baselines <set>  Generate a particular set of regression tests
#   sets             Get a list of all baseline sets

CFG_TESTS="simple.bp simple.c irreducible.bp selfref.bp"

DIR=`dirname $0`
REGRESSION_TXT="$DIR/regression.txt"
RUN="$DIR/regression -loadpath $DIR/.."
RUN_MAIN="$DIR/../duet -loadpath $DIR/.."

phase () {
    NAME=$1
    NAME_LENGTH=`echo $NAME | wc -c`
    PADDING=`yes - | head -$((75 - $NAME_LENGTH)) | tr -d '\n'`
    echo ---- $NAME $PADDING
}

run_all () {
    NAME=$1
    shift
    CMD=$1
    shift
    PASSED=0
    FAILED=0
    phase $NAME
    for x in $@; do
	OUT=`$RUN $CMD $x | tail -1`
	case $OUT in
	    "Passed")
		PASSED=$(($PASSED+1))
		;;
	    "Failed")
		FAILED=$(($FAILED+1))
		echo Baselines differ at $x
		;;
	    *)
		echo Error at $x
		;;
	esac
    done
    echo "Passed: $PASSED"
    echo "Failed: $FAILED"
}

run_all_txt () {
    RUN_FAMILY=$1
    PASSED=0
    FAILED=0
    phase $RUN_FAMILY regression tests
    WORKING="$DIR/working"
    if [ -d $WORKING ]; then
	find $WORKING -name "*.working" | xargs rm -f
	find $WORKING -name "*.diff" | xargs rm -f
    else
	mkdir $WORKING
    fi

    while read x; do
	FAMILY=`echo $x | awk '//{print $1}'`
	if [ "$FAMILY" != "$RUN_FAMILY" ]; then
	    continue
	fi
	TEST=`echo $x | awk '//{print $2}'`
	FLAGS=`echo $x | sed 's/[^ ]* [^ ]* //'`
	FAM_DIR="$DIR/$FAMILY"
	WORKING_FAM_DIR="$WORKING/$FAMILY"
	if [ ! -d $WORKING_FAM_DIR ]; then
	    echo Make $WORKING_FAM_DIR
	    mkdir $WORKING_FAM_DIR
	fi
	echo Running $TEST [$FAMILY]...
	WORKING_OUTPUT="$WORKING_FAM_DIR/$TEST.working"
	BASELINE="$FAM_DIR/baselines/$TEST.baseline"
	$RUN_MAIN $FLAGS $FAM_DIR/code/$TEST > $WORKING_OUTPUT
	DIFF_COUNT=`diff $BASELINE $WORKING_OUTPUT | wc -l`
	if [ $DIFF_COUNT -gt 0 ]; then
	    echo Baseline differs!
	    diff $BASELINE $WORKING_OUTPUT > $WORKING_FAM_DIR/$TEST.diff
	    cat $WORKING_FAM_DIR/$TEST.diff
	    FAILED=$(($FAILED+1))
	else
	    PASSED=$(($PASSED+1))
	fi
    done < <(cat $REGRESSION_TXT)
    echo "Passed: $PASSED"
    echo "Failed: $FAILED"
}

regression_sets () {
    awk '//{print $1}' $REGRESSION_TXT | sort | uniq
}

generate_all () {
    CMD=$1
    shift
    for x in $@; do
	echo Generating baseline for $x...
	$RUN $CMD $x
    done
}

generate_all_txt () {
    GENERATE_FAMILY=$1
    cat $REGRESSION_TXT | while read x; do
	FAMILY=`echo $x | awk '//{print $1}'`
	if [ "$FAMILY" != "$GENERATE_FAMILY" ]; then
	    continue
	fi
	TEST=`echo $x | awk '//{print $2}'`
	FLAGS=`echo $x | sed 's/[^ ]* [^ ]* //'`
	FAM_DIR=$DIR/$FAMILY
	echo Generating baseline for $TEST [$FAMILY]...
	$RUN_MAIN $FLAGS $FAM_DIR/code/$TEST > $FAM_DIR/baselines/$TEST.baseline
    done
}

if [ $# -lt 1 ]; then
    FLAG=run
else
    FLAG=$1
fi
shift
if [ $# -lt 1 ]; then
    SETS=`regression_sets`
else
    SETS=$@
fi


case $FLAG in
    "run")
	echo Running regression tests...
	for s in $SETS; do
	    run_all_txt $s
	done
	;;
    "baselines")
	echo Generating baselines...
	for s in $SETS; do
	    generate_all_txt $s
	done
	;;
    "sets")
	echo Regression test sets:
	regression_sets
	;;
    *)
	echo Command $FLAG not found
	;;
esac
