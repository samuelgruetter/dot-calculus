#!/bin/bash

# NOTE: the current version does not seem to include COQBIN path from settings.sh

###################################################################

# ./fix.sh  has the same behavior has 'make' except that it opens
# the files that do not compile using ./open.sh

###################################################################

# You can add/remove the option "-j" after make
MAKE="make -j"

# If you use the -j options, you might get several errors in parallel.
# By default, all the files with errors will be opened. If you want 
# at most one file to be opened, define ONLY_ONE to be any nonempty string 
ONLY_ONE=

# Execution of the make command

RESULT="fix_sh_compil.txt"
$MAKE $* | tee $RESULT
TEXT=`cat $RESULT`

# Parsing of the output
 
PATTERN="File \"([^\"]*)\", line"
while read LINE; do
   if [[ $LINE =~ $PATTERN ]]; then
      n=${#BASH_REMATCH[*]}
      if [[ 0 -lt $n ]]; then
         FILE=${BASH_REMATCH[1]}
         echo "Error in: ${FILE}"
         nohup ./open.sh $FILE >/dev/null 2>&1 &
         if [ "$ONLY_ONE" != "" ]; then 
            break
         fi
      fi
   fi
done < $RESULT

# Deletion of the auxiliary file used to store the compilation result

if [ -f $RESULT ]; then
   rm $RESULT
fi

