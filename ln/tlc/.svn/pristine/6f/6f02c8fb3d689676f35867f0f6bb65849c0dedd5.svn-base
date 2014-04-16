
############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#     COQBIN=/var/tmp/charguer/v8.4/bin/
# Note the use of a leading slash.

COQBIN=

-include settings.sh

#######################################################
# BINARIES

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

#######################################################
# FILES

LIB=\
	LibTactics.v \
	LibAxioms.v \
	LibEqual.v \
	LibLogic.v \
	LibEpsilon.v \
	LibFunc.v \
	LibChoice.v \
	LibOperation.v \
	LibBool.v \
	LibReflect.v \
	LibUnit.v \
	LibProd.v \
	LibSum.v \
	LibOption.v \
	LibStruct.v \
	LibRelation.v \
	LibOrder.v \
	LibWf.v \
	LibNat.v \
	LibInt.v \
	LibStruct.v \
	LibList.v \
	LibListSorted.v \
	LibListZ.v \
	LibBag.v \
	LibSet.v \
	LibMultiset.v \
	LibMap.v \
	LibArray.v \
	LibGraph.v \
	LibPer.v \
	LibString.v \
	LibFset.v \
	LibVar.v \
	LibEnv.v \
	LibLN.v \
	LibHeap.v \
	LibCore.v 

#	LibBigop.v \
#  LibQuotient.v \
#	LibOperator.v \
#	LibGroup.v \
#	LibFset.v \
#	LibEnv.v \
#	LibRelationb.v \
#	LibRing.v \
#	LibMonoid.v \
#	LibAtom.v \
#	LibData.v \

EXTRA=\
	LibFix.v \
	LibStream.v 

DEMO=\
	LibTacticsDemos.v \
	LibFixDemos.v \
	LibOtherDemos.v 

#	LibCoreDemos.v \

TACTICS=\
	LibTactics.v \
	LibTacticsDemos.v 

ALL= $(LIB) $(EXTRA) $(DEMO)


#######################################################
# TARGETS

.SUFFIXES: .v .vo
.PHONY: all lib demo depend

all: $(ALL:.v=.vo) 
lib: $(LIB:.v=.vo) 
extra: $(EXTRA:.v=.vo)
demo: $(DEMO:.v=.vo) 
tactics: $(TACTICS:.v=.vo)
depend: .depend

.v.vo : .depend
	$(COQC) $<


#######################################################
#DEPENDENCIES

.depend : $(ALL)
	$(COQDEP) -I . $(ALL) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif

#######################################################
#CLEAN

clean:
	@rm -f *.vo || echo ok
	@rm -f .depend || echo ok


