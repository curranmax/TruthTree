from truthtree import *
import argparse

parser = argparse.ArgumentParser(description='Process data stored in a file')
parser.add_argument('ifile', metavar='F', type=str, nargs=1,help='path of file where data is')
parser.add_argument('ofile', metavar='F', type=str, nargs=1,help='path of file to write to')

#Reads in a tree from an arguement file, then calls the run function which automatically splits expressions and then writes the tree to an action file

ifname=parser.parse_args().ifile[0]
ofname=parser.parse_args().ofile[0]

ttree=TruthTree()
ttree.readArguementIn(ifname)
ttree.run()
printTruthTree(ttree)
writeTreeToFile(ttree,ofname)