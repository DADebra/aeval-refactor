#!/bin/sh

if [ -z "$__SCHEDULER_SH__" ]; then
__SCHEDULER_SH__=1

#set -x

# A job scheduler which can schedule several (potentially-multicore) jobs
# (i.e. shell code) to the CPU's N cores.
# Intended to be used as a library for more featured applications.

### PUBLIC INTERFACE ###

# Job Start Callback interface:
# $1 = Job ID just started
# $2 = PID of running process
# $3 = Temp file of job's stdout (don't remove)
# $4 = Temp file of job's stderr (don't remove)

# Job Done Callback interface:
# $1 = Job ID that finished
# $2 = Exit code of job's command
# $3 = Time job took to complete in seconds (includes decimal)
# $4 = Temporary file containing job's stdout (don't need to clean up)
# $5 = Temporary file containing job's stderr (don't need to clean up)
# e.g. 'callback 0 0 1.5 /tmp/tmp.QJSK /tmp/tmp.KDIA'
# Note that if callback definition includes arguments, the above arguments
#   are appended to the end. So if you do include arguments, a 'shift N'
#   is recommended for N = # of arguments you passed to 'addjob'.

# Adds a job to be run on 'runjobs'
# $1 = job (use 'trcmd' to delimit arguments)
# $2 = expected # of cores taken up
# $3 = callback to run after starting job (use 'trcmd')
# $4 = callback to run when job is done (use 'trcmd')
# Job ID of new job is exported as 'jobid' variable
addjob() {
  if [ $# -lt 4 ]
  then
      echo "addjob takes 4 parameters"
      exit 4
  fi
  scheduler_addjob "$1" "$2" "$3" "$4"
}

# Runs all defined jobs, taking up at most $1 CPU cores.
runjobs() {
  if [ $# -lt 1 ]
  then
      echo "runjobs takes 1 parameter"
      exit 4
  fi
  scheduler_runjobs "$1" < "$scheduler_jobs"
}

# Separates $@ by ^_ for consumption by this script
trcmd() {
    out=""
    for arg
    do
        out="$out$arg"
    done
    echo "$out"
}

### PRIVATE CODE ###

scheduler_nextjobid=0
scheduler_numrunning=0
scheduler_runningpids=""

haveatexit() { hash atexit >/dev/null 2>&1; return $?; }

export scheduler_jobs="$(mktemp)"
echo "$scheduler_jobs"
haveatexit && atexit rm -f "$scheduler_jobs"

scheduler_addjob() {
    export jobid=$scheduler_nextjobid
    echo "$jobid$1$2$3$4" >> "$scheduler_jobs"
    scheduler_nextjobid=$(( $scheduler_nextjobid + 1 ))
}

# Check all running job PIDs, to see if they're done, and handle their
#   completion if so.
# Returns 0 (true) if at least one job finished.
scheduler_checkjobsdone() {
    if [ -z "$scheduler_runningpids" ]
    then
        return 0
    fi
    local scpid sccallback scoutfile scerrfile sctimefile scparallel sccallback
    local jobsdone newpids scoldifs
    jobsdone=0
    newpids=""
    scoldifs="$IFS"
    IFS=""
    for entry in $scheduler_runningpids
    do
        IFS=""
        set -- $entry
        IFS="$scoldifs"
        scpid="$1"; scjid="$2"; scoutfile="$3"; scerrfile="$4"; sctimefile="$5";
        scparallel="$6"; sccallback="$7";
        if ! ps -p "$scpid" >/dev/null
        then
            wait "$scpid" >/dev/null 2>&1
            scret=$?
            sctimetaken="$(cat "$sctimefile")"
            rm "$sctimefile"

            IFS=""
            set -- $sccallback
            IFS="$scoldifs"
            "$@" "$scjid" "$scret" "$sctimetaken" "$scoutfile" "$scerrfile"
            rm -f "$scoutfile" "$scerrfile"

            jobsdone=$(( $jobsdone + $scparallel ))
        else
            newpids="$newpids$entry"
        fi
        IFS=""
    done
    IFS="$scoldifs"

    scheduler_runningpids="$newpids"
    
    if [ $jobsdone -ne 0 ]
    then
        scheduler_numrunning=$(( $scheduler_numrunning - $jobsdone ))
        if [ $scheduler_numrunning -lt 0 ]
        then
            echo "ERROR: numjobs is less than 0 ($scheduler_numrunning)"
            scheduler_numrunning=0
        fi
        return 0
    else
        return 1
    fi
}

# Time the execution of the command specified by "$@", outputting results to
# $1 (i.e. "$@" starts at arg 2)
scheduler_timecmd() {
    outfile="$1"
    shift 1
    start="$(gettime)"
    ("$@")
    ret=$?
    end="$(gettime)"
    diff="$(difftime "$end" "$start")"
    echo "$diff" > "$outfile"
    return $ret
}

scheduler_runjobs() {
  local numcpus="$1"
  local oldifs="$IFS"
  while read job
  do
      IFS=""
      set -- $job
      IFS="$oldifs"
      local nextjid nextjobcmd nextparallel nextstartcallback nextdonecallback
      nextjid="$1"; nextjobcmd="$2"; nextparallel="$3"; nextstartcallback="$4";
      nextdonecallback="$5";
      while [ $(( $scheduler_numrunning + $nextparallel )) -gt $numcpus ]
      do
          sleep 0.1
          if scheduler_checkjobsdone
          then
              if [ $scheduler_numrunning -eq 0 -a $nextparallel -gt $numcpus ]
              then
                  echo "WARNING: Job ID $nextjid uses $nextparallel CPU cores but we only have $numcpus. Running anyways."
                  break
              fi
          fi
      done
      # Can now start new job

      # Will all be cleaned up by checkjobsdone
      local timefile="$(mktemp)"
      local outfile="$(mktemp)"
      local errfile="$(mktemp)"
      haveatexit && atexit rm -f "$timefile" "$outfile" "$errfile"
      IFS=""
      set -- $nextjobcmd
      IFS="$oldifs"
      scheduler_timecmd "$timefile" "$@" > "$outfile" 2> "$errfile" &
      local pid=$!
      scheduler_runningpids="$scheduler_runningpids$pid$nextjid$outfile$errfile$timefile$nextparallel$nextdonecallback"
      scheduler_numrunning=$(( $scheduler_numrunning + $nextparallel ))

      IFS=""
      set -- $nextstartcallback
      IFS="$oldifs"
      "$@" "$nextjid" "$pid" "$outfile" "$errfile"
  done
  IFS="$oldifs"

  # Wait for all tests to finish running.
  while :
  do
      sleep 1
      scheduler_checkjobsdone
      if [ $scheduler_numrunning -eq 0 ]
      then
          break
      fi
  done
}

fi
