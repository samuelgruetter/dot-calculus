COQBIN=
if [ -f settings.sh ]
then
    source settings.sh 
fi
${COQBIN}coqide -dont-load-proofs $*
