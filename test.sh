#!/bin/bash

timeout=10
rating_timeout=1800
domains="miconic smartphone satellite umtranslog woodworking zenotravel childsnack rover barman transport blocksworld factories entertainment" 

function rating() {
    time="$1"
    if (( $(echo "$time <= 1"|bc -l) )); then
        echo "1"
    else 
        r=$(echo "1 - l($time) / l($rating_timeout)"|bc -l)
        if (( $(echo "$r > 1"|bc -l) )); then
            echo "1"
        else
            echo "$r"
        fi
    fi
}

function end() {
    echo "$solved/$all solved within $timeout seconds. Score w.r.t. ${rating_timeout}s as actual timeout: ${green}$score${reset}."
    exit $1
}

exit_on_error=true
exit_on_verify_fail=true

set -e
set -o pipefail
trap 'echo "Interrupted."; end 1' INT

red=`tput setaf 1`
green=`tput setaf 2`
yellow=`tput setaf 3`
blue=`tput setaf 4`
reset=`tput sgr0`

solved=0
unsolved=0
all=0
score=0

# Count instances
for domain in $domains ; do    
    for pfile in instances/$domain/p*.hddl; do
        all=$((all+1))
    done
done

# Attempt to solve each instance
for domain in $domains ; do
    dfile=instances/$domain/domain.hddl
    
    for pfile in instances/$domain/p*.hddl; do
        
        logdir="logs/${BASHPID}/${domain}_$(basename $pfile .hddl)_$@_$(date +%s)/"
        mkdir -p "$logdir"
        outfile="$logdir/OUT"
        verifile="$logdir/VERIFY"
        
        set +e
        echo -ne "[$((solved+unsolved))/$all] Running treerexx on ${blue}$pfile${reset} ... "

        start=$(date +%s.%N)
        /usr/bin/timeout $timeout ./treerexx $dfile $pfile $@ > "$outfile" & wait -n
        retval="$?"
        end=$(date +%s.%N)    
        runtime=$(python -c "print(${end} - ${start})")

        if [ "$retval" == "0" ]; then
            echo -ne "exit code ${green}$retval${reset}. "
            score=$(echo $score + $(rating "$runtime")|bc -l)
        else
            echo -ne "${yellow}exit code $retval.${reset} "
            if [ "$retval" == "134" -o "$retval" == "139" ]; then
                if $exit_on_error ; then
                    echo "${red}Exiting.${reset}"
                    end 1
                fi
            fi
        fi
        set -e
        
        if cat "$outfile"|grep -q "<=="; then
            echo -ne "Verifying ... "
            ./pandaPIparser $dfile $pfile -verify "$outfile" > "$verifile"
            if grep -q "false" "$verifile"; then
                echo -ne "${red}Verification error!${reset}"
                if $exit_on_verify_fail ; then
                    echo " Output:"
                    cat "$verifile"
                    exit 1
                else
                    echo ""
                fi
            else
                echo "${green}All ok.${reset}"
            fi
            solved=$((solved+1))
        else
            echo ""
            unsolved=$((unsolved+1))
        fi
    done
done

end 0
