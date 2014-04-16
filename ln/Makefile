############################################################################
# You can define your own path to COQBIN and to TLC by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# TLC=~/tlc/trunk
# COQBIN=/var/tmp/coq-8.3pl2/bin/
#
# Note that TLC should have no leading slash, whereas COQBIN should have one.
# Note that if you rebind COQBIN you need to do the same in the TLC folder.
# Note that if you add a settings.sh file, you will need to do "make depend".

# Default paths are as follows:

TLC=tlc
COQBIN=

-include settings.sh


############################################################################

INCLUDES=-I . -I $(TLC)

COQC=$(COQBIN)coqc -dont-load-proofs $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc --quiet --utf8 --html

############################################################################
# STABLE DEVELOPMENTS

CORE=\
	STLC_Core_Definitions \
	STLC_Core_Infrastructure \
	STLC_Core_Soundness \
	STLC_Core_Adequacy \
	STLC_Core_FullBeta \
	STLC_Core_Light \
	STLC_Core_Tutorial
BIG=\
	BigStep_Definitions \
	BigStep_Infrastructure \
	BigStep_Equivalence 
FSUB=\
	Fsub_Definitions \
	Fsub_Infrastructure \
	Fsub_Soundness 
COC=\
	CoC_Definitions \
	CoC_Infrastructure \
	CoC_BetaStar \
	CoC_ChurchRosser \
	CoC_Conversion \
	CoC_Preservation 
ML=\
	ML_Definitions \
	ML_Infrastructure \
	ML_Soundness 
EXN=\
	STLC_Exn_Definitions \
	STLC_Exn_Infrastructure \
	STLC_Exn_Soundness 
REF=\
	STLC_Ref_Definitions \
	STLC_Ref_Infrastructure \
	STLC_Ref_Soundness 
COREWF=\
	STLC_Core_WF_Definitions \
	STLC_Core_WF_Infrastructure \
	STLC_Core_WF_Soundness 
DATA=\
	STLC_Data_Definitions \
	STLC_Data_Infrastructure \
	STLC_Data_Soundness 
CPS=\
	CPS_Definitions \
	CPS_Infrastructure \
	CPS_Correctness 
PAT=\
	STLC_Pat_Definitions \
	STLC_Pat_Infrastructure \
	STLC_Pat_Soundness 
LAMBDA=\
	Lambda_Definitions \
	Lambda_Infrastructure \
	Lambda_ChurchRosser 
JAR=\
	Lambda_JAR_paper 
MLCORE=\
	ML_Core_Definitions \
	ML_Core_Infrastructure \
	ML_Core_Soundness 
ISK=\
   ISK_Confluence

ALL=$(BIG) $(EXN) $(REF) $(CORE) $(CPS) $(ISK) $(LAMBDA) $(COC) $(ML) $(FSUB) $(JAR)
	
# The following developments need to be updated to the new library
#   STLC_Core_WF
#   STLC_Data
#   STLC_Pat (needs a few patches)
#   ML_Core => needs to move from List to LibList as done in $(ML)

NOT_COMPILING= $(COREWF) $(DATA) $(PAT) $(MLCORE)


############################################################################
# EXPERIMENTAL DEVELOPMENTS


# The following developments are experimental and are not complete

PATOPEN=\
	STLC_PatOpen_Definitions \
	STLC_PatOpen_Infrastructure \
	STLC_PatOpen_Soundness 
MUT=\
	STLC_Mut_Definitions \
	STLC_Mut_Infrastructure \
	STLC_Mut_Soundness

EXPERIMENTAL= $(MUT) $(PATOPEN)


############################################################################

ALL_SRC=$(ALL:=.v)
TLC_SRC=$(wildcard $(TLC)/*.v)
DEP_SRC=$(ALL_SRC) $(TLC_SRC)

.PHONY: all tlc clean 
.SUFFIXES: .v .vo 

all: $(ALL:=.vo)

tlc: 
	make -C $(TLC) lib

.v.vo : .depend
	$(COQC) $<

core: $(CORE:=.vo)
big: $(BIG:=.vo) 
mut: $(MUT:=.vo) 
fsub: $(FSUB:=.vo) 
coc: $(COC:=.vo) 
ml: $(ML:=.vo) 
exn: $(EXN:=.vo) 
ref: $(REF:=.vo) 
corewf: $(COREWF:=.vo)
data: $(DATA:=.vo) 
cps: $(CPS:=.vo) 
isk: $(ISK:=.vo) 
pat: $(PAT:=.vo) 
patopen: $(PATOPEN:=.vo) 
lambda: $(LAMBDA:=.vo)
mlcore: $(MLCORE:=.vo)


#######################################################

depend: .depend

.depend : $(DEP_SRC) Makefile
	$(COQDEP) $(DEP_SRC) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif

clean :
	rm -f *.vo .depend *.deps *.dot *.glob
	@rm -f $(TLC)/*.vo $(TLC)/*.glob $(TLC)/*.v.d || echo ok  

############################################################################
#
#coqdoc :
#	@mkdir -p doc_light
#	$(COQDOC) --gallina -d doc_light $(VFILES)
#




