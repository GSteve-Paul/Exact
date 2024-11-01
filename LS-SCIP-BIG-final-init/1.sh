#!/bin/bash
FNAME=$1
TOTAL_TIME_LIMIT=$2
TEMP_DIR=$3

# 确保临时目录存在，如果不存在则创建它
mkdir -p "$TEMP_DIR"

# 在临时目录内创建一个临时文件名
TEMP_FILE_NAME1="$TEMP_DIR/outFirstProgram.txt"
TEMP_FILE_NAME2="$TEMP_DIR/outSecondProgram.txt"

# 将时间限制分为两等分
TIME_LIMIT=$((TOTAL_TIME_LIMIT / 2))

TFIRST=$TIME_LIMIT
TSECOND=$TIME_LIMIT

timeout -s 15 $TFIRST ./COM-Pre $FNAME -total-t=$TFIRST -no-par -pre-lim=100 -mem-lim=40000 -v0 > $TEMP_FILE_NAME1
CODE1=$?

timeout -s 15 $TSECOND ./Exact $FNAME --verbosity=0 --format=opb --bits-overflow=64 --print-uniform=0 --print-sol > $TEMP_FILE_NAME2
CODE2=$?

# Function to decide which file to output based on the contents
function decide_output {
    local status1=$(grep '^s' "$TEMP_FILE_NAME1" | tail -n 1 | awk '{print $2}')
    local status2=$(grep '^s' "$TEMP_FILE_NAME2" | tail -n 1 | awk '{print $2}')

    # Check for "OPTIMUM FOUND" or "UNSATISFIABLE"
    if [[ "$status1" == "OPTIMUM FOUND" ]] || [[ "$status1" == "UNSATISFIABLE" ]]; then
        cat "$TEMP_FILE_NAME1"
        return
    elif [[ "$status2" == "OPTIMUM FOUND" ]] || [[ "$status2" == "UNSATISFIABLE" ]]; then
        cat "$TEMP_FILE_NAME2"
        return
    fi

    # Check for "SATISFIABLE"
    if [[ "$status1" == "SATISFIABLE" ]] && [[ "$status2" == "SATISFIABLE" ]]; then
        local value1=$(grep '^o' "$TEMP_FILE_NAME1" | tail -n 1 | awk '{print $2}')
        local value2=$(grep '^o' "$TEMP_FILE_NAME2" | tail -n 1 | awk '{print $2}')
        if (( value1 < value2 )); then
            cat "$TEMP_FILE_NAME1"
        else
            cat "$TEMP_FILE_NAME2"
        fi
        return
    elif [[ "$status1" == "SATISFIABLE" ]]; then
        cat "$TEMP_FILE_NAME1"
        return
    elif [[ "$status2" == "SATISFIABLE" ]]; then
        cat "$TEMP_FILE_NAME2"
        return
    fi

    # Default case
    cat "$TEMP_FILE_NAME1"
}

# Decide output based on the codes and file contents
if [ $CODE1 -eq 124 ] && [ $CODE2 -eq 124 ]; then
    decide_output
elif [ $CODE1 -eq 124 ] || [ $CODE1 -eq 0 ]; then
    echo "c Solved by Second Program"
    cat $TEMP_FILE_NAME2
else
    echo "c Solved by First Program"
    cat $TEMP_FILE_NAME1
fi
