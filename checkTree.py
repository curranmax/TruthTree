#! /usr/bin/env python

from truthtreechecker import *
import argparse

parser = argparse.ArgumentParser(description='Process data stored in a file')
parser.add_argument('tfile', metavar='TF', type=str, nargs=1,help='file with the action data')
parser.add_argument('checkfile', metavar='CF', type=str, nargs=1,help='file with the arguement the tree should be using')
parser.add_argument('exprnum', metavar='n', type=int, nargs=1,help='index of file in checkfile')


#Given an action file, and an arguement file, this will check if the tree was correctly formed
#The arguement file is just to make sure the arguement was entered correctly, so if this was a hw assignment that the person actually did the correct problem
#The action file gives all the details of how the tree was formed, including when expressions were split and when branches were closed

tfname=parser.parse_args().tfile[0]
cfname=parser.parse_args().checkfile[0]
exprnum=parser.parse_args().exprnum[0]
checker=TotalCheckTree(tfname,cfname,exprnum)
