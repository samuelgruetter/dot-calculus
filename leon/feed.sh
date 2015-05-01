#!/bin/bash

#usage: feed.sh srcfile

# needs
# sudo apt-get install inotify-tools

if [ $# -ne 1 ] ; then
	echo "USAGE: feed.sh srcfile"
	exit
fi

srcfilerel=$1

srcfile=`readlink -f $srcfilerel`

while true; do
	#inotifywait -e close_write,moved_to,create $srcfile >/dev/null 2>/dev/null
	inotifywait -e close_write $srcfile >/dev/null 2>/dev/null
	printf "\033c"
  ~/Documents/git/leon/leon --timeout=3 $srcfile
done

