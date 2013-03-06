from truthtree import *
import argparse

parser = argparse.ArgumentParser(description='Process data stored in a file')
parser.add_argument('tfile', metavar='TF', type=str, nargs=1,help='file with the tree data')
parser.add_argument('checkfile', metavar='CF', type=str, nargs=1,help='file with the arguement the tree should be using')

#Given an action file, and an arguement file, this will check if the tree was correctly formed
#The arguement file is just to make sure the arguement was entered correctly, so if this was a hw assignment that the person actually did the correct problem
#The action file gives all the details of how the tree was formed, including when expressions were split and when branches were closed

def checkTree(fname,checkfile):
	#Constructs the tree from the actoin file
	ttr=TruthTreeReader(fname)
	#Reads in the arguement file
	#The atoms are shared from those in the TruthTreeReader so that atom equality is by pointer
	lr=LogicReader(checkfile,atoms=ttr.atoms)

	#checks that there is a one to one match between the premises of the action and arguement file
	#this is probably not the best way and may
	tes=ttr.premises
	inds=[]
	if len(tes)!=len(lr.expressions[:-1]):
		print "The tree doesn't have the correct setup"
		return
	for ce in lr.expressions:
		match=False
		for i,te in enumerate(tes):
			if ce.equals(te) and not(i in inds):
				match=True
				inds.append(i)
				break
		if not match:
			print "The tree doesn't have the correct setup"
			return
	if not(ttr.conclusion.equals(lr.expressions[-1])):
		print "The tree doesn't have the correct setup"
		return

	#Gets the actual tree and one by one applies the forward actions to the tree and makes sure they are valid
	ttree=ttr.tree
	for a in ttr.factions:
		r=ttree.applyForwardAction(a)
		if not r:
			printTruthTree(ttree)
			print "The tree is not correct, failed on",a.opnum
			return
	print "THE TREE IS CORRECT"
	printTruthTree(ttree)

tfname=parser.parse_args().tfile[0]
cfname=parser.parse_args().checkfile[0]
checkTree(tfname,cfname)
