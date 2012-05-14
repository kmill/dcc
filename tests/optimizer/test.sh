#!/bin/sh

domidirc=0
base=`dirname $0`

if uname -a | grep "Darwin" > /dev/null; then
    echo "(compiling for Mac OS X)"
    d=`pwd`
    cd $base/maclib
    make
    cd $d
    archstring="-arch x86_64"
    dccopt="--mac"
    lib="$base/maclib/lib6035.o"
    LD_LIBRARY_PATH=$base/maclib:$LD_LIBRARY_PATH
else
    d=`pwd`
    cd $base/lib
    make
    cd $d
    archstring=""
    dccopt=""
    lib="-L$base/lib -l6035 -lpthread"
    if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
  echo "Refusing to run cross-compilation on non-64-bit architechure."
  exit 0;
    fi
fi


runcompiler_opt() {
    $base/../../dcc -r -target codegen -opt all -o $2 $1
}

runcompiler_unopt() {
    $base/../../dcc -target codegen -opt none -o $2 $1
}


isolate() {
  exec 3>/dev/stderr 2>/dev/null
  if $*; then
    exec 3>&2
    return 0
  else
    exec 3>&2
    return 1
  fi
}

fail=0


cd `dirname $0`
orig_pwd=$PWD
for file in $PWD/input/*.dcf; do
  workingdir=`mktemp -d`
  progname=`basename $file .dcf`
  input_filename="`echo $progname|cut -d_ -f1`.pgm"
  orig_input="${orig_pwd}/data/$input_filename"
  input="${workingdir}/$input_filename"
  golden="${orig_pwd}/output/${progname}.pgm"
  binary="${workingdir}/${progname}"
  asm="${workingdir}/${progname}.s"
  output="${workingdir}/${progname}.pgm"
  timing_opt="${workingdir}/${progname}_opt.timing"
  timing_unopt="${workingdir}/${progname}_unopt.timing"
  echo $input_filename
  cp $orig_input $input;
  msg=""
  if runcompiler_opt $file $asm; then
    if gcc $archstring -o $binary $asm $lib -l6035 -lpthread; then
      cd $workingdir
      if $binary > $timing_opt; then
        if ! diff -q $output $golden > /dev/null; then
          msg="File $file output mismatch.";
        fi
      else
        msg="Program failed to run.";
      fi
    else
      msg="Program failed to assemble.";
    fi
  else
    msg="Program failed to generate assembly.";
  fi
  cd "$orig_pwd";
  if runcompiler_unopt $file $asm; then
    if gcc -o $binary $asm $lib -l6035 -lpthread; then
      cd $workingdir
      if $binary > $timing_unopt; then
        if ! diff -q $output $golden > /dev/null; then
          msg="File $file output mismatch.";
        fi
      else
        msg="Program failed to run.";
      fi
    else
      msg="Program failed to assemble.";
    fi
  else
    msg="Program failed to generate assembly.";
  fi
  echo $file
  if [ ! -z "$msg" ]; then
    fail=1
    echo $msg
  else
    if [ ! -z "`cat $timing_unopt`" ]; then
      echo -n "Unoptimized: "
      unopt=`cat $timing_unopt|awk '{print($2)}'`
      echo "${unopt} usec"
    fi
    if [ ! -z "`cat $timing_opt`" ]; then
      echo -n "Optimized: "
      opt=`cat $timing_opt|awk '{print($2)}'`
      echo "${opt} usec"
    fi
  fi
  int_speedup=$(($unopt / $opt)) 
  dec_speedup=$((($unopt * 1000) / $opt - ($int_speedup * 1000))) 
  printf "%d.%03dx speedup\n" $int_speedup ${dec_speedup}

  cd "$orig_pwd";
  rm -r -f $workingdir;
done

exit $fail;
