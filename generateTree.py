#! /usr/bin/env python

from truthtreegen import *
from iologic import MultiLogicReader
import argparse

parser = argparse.ArgumentParser(description='Process data stored in a file')
parser.add_argument('ifile', metavar='IF', type=str, nargs=1,help='path of file where data is')
parser.add_argument('-ofile', metavar='OF', type=str, nargs=1,help='path of file to write to')
parser.add_argument('-exprnum', metavar='IND', type=int, nargs=1,help='Index for expression to run')

#Reads in a tree from an arguement file, then calls the run function which automatically splits expressions and then writes the tree to an action file

ifname=parser.parse_args().ifile[0]
ofile=None
exprnum=None
if parser.parse_args().ofile:
	ofile=parser.parse_args().ofile[0]
if parser.parse_args().exprnum:
	exprnum=parser.parse_args().exprnum[0]
	exprnum=exprnum-1

reader=MultiLogicReader(ifname,{"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"Atom":AtomGenTT,"FOAtom":FOAtomGenTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalGenTT,"Existential":ExistentialGenTT})
if exprnum==None:
	for i,es in enumerate(reader.expressions):
		ttree=TotalTruthTree()
		ttree.setPsandC(es,reader.allunboundconstants[i])
		ttree.run()
		ttree.printValidity(str(i+1)+")")
else:
	ttree=TotalTruthTree()
	ttree.setPsandC(reader.expressions[exprnum],reader.allunboundconstants[exprnum])
	ttree.run()
	ttree.printValidity(str(exprnum+1)+")")
	ttree.printTree()
	if ofile!=None:
		ttree.writeTree(ofile)