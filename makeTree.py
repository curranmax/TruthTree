from truthtree import *
from iologic import *
import sys
import argparse

#This allowsa command line creation of trees
#I made this as a way to start checking the checker, it should never be used as a way to efficently make trees

parser = argparse.ArgumentParser(description='Process data stored in a file')
parser.add_argument('ifile', metavar='F', type=str, nargs=1,help='path of file where data is')
parser.add_argument('ofile', metavar='F', type=str, nargs=1,help='path of file to write to')

#input function
#I am using 2.7 so this works, but in 3.x it is different so tha tis why i map it to a variable
infun=raw_input

#Makes a truth tree from the command line
#One note, the right and left are swapped so if you use this, be aware of that
#Can be used as a model for a ui driven tree maker
class TruthtreeCommadLine:
	def __init__(self,tree,ofile):
		self.tree=tree
		self.ofile=ofile
		self.exprparser=LogicString(constructors={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT},atoms=self.tree.atoms)
		self.prompt=">>"
		self.commands={"h":("Help",self.printCommands),"s":("Split",self.split),"c":("Close Leaf",self.closeLeaf),"o":("Open Leaf",self.openLeaf),"q":("Quit",self.quit),"p":("Print Tree",self.printTree),"w":("Write Tree to file",self.writeTree)}

	#call this to start
	def makeTree(self):
		#Lets the user enter a command and then calls its associated function
		#The commands are stored in the self.commands dictionary
		print "Enter 'h' anytime to show commands that can be used"
		while True:
			i=self.getInput()
			if i in self.commands:
				r=self.commands[i][1]()
				if not r:
					return
			else:
				print "Invalid input"

	#Prints a dictionary, where the key is the command, and the value is a two-tuple, first one is the description of the comand and the second is used for something else
	def printCommands(self,com=None,expl="The commands are as follows:"):
		if com==None:
			#default value
			com=self.commands
		#Explains what the commands are
		print expl
		#figures out the numberof spaces needed so everything looks nice
		nt=int(max([(len(com[k][0])+2) for k in com.keys()])/8)
		for k in com.keys():
			t="\t"*(nt-int((len(com[k][0])+2)/8)+1)
			print com[k][0]+": "+t+k
		return True

	#let's the user choose an expression split it and put those expressions in the tree
	#very verbose, because i wanted to introduce weird errors to see if the checker would notice it
	def split(self):
		#Asks for the user to input the branch where the split will occur
		#Then for the expression
		#Then it will continaully query the user for a destination and the expression to put there
		print "Enter the Branch where the expression in question is"
		i=self.getInput(2)
		splittree=self.tree.getTreeSection(i)
		if splittree==None:
			print "Invalid tree section"
			return True
		print "Please enter the expression you want to split"
		for e in splittree.expressions:
			print e.toString()
		try:
			sue=self.exprparser.parseString(self.getInput(2))
		except IOError:
			print "Invalid expression"
			return True
		m=False
		for e in splittree.expressions:
			if e.equals(sue):
				m=True
				break
		if not m:
			print "Expression not in Tree Branch"
			return True
		print "Enter all destination trees then the expression that goes there"
		dts=[]
		des=[]
		self.printTree()
		while True:			
			print "Enter a destination tree branch, input p to display tree, and anything else to stop"
			dt=self.getInput(2)
			if dt[0]!='h':
				break
			print "Enter expression at the above destination"
			try:
				de=self.exprparser.parseString(self.getInput(2))
			except IOError:
				print "Invalid expression"
				return True
			dts.append(dt)
			des.append(de)
		if not splittree.userSplit(sue,dts,des):
			print "Error in performing split"
			return True
		self.printTree()
		return True

	#Lets the user set a branch to closed
	def closeLeaf(self):
		print "Enter the tree string for the leaf you wish to close"
		i=self.getInput(2)
		leaf=tree.getTreeSection(i)
		if leaf==None:
			print "Invalid input"
			return True
		else:
			leaf.setClosed()
		self.printTree()
		return True

	#Let's the user set a branch to ope 
	def openLeaf(self):
		print "Enter the tree string for the leaf you wish to open"
		i=self.getInput(2)
		leaf=tree.getTreeSection(i)
		if leaf==None:
			print "Invalid input"
			return True
		else:
			leaf.setOpen()
		self.printTree()
		return True

	#quits
	def quit(self):
		return False

	#Prints the tree at a point
	def printTree(self):
		printTruthTree(self.tree)
		print ""
		return True

	#Writes the action file for the tree
	def writeTree(self):
		wcom={"v":("Valid",0),"i":("Invalid",0),"n":("Neither",0)}
		self.printCommands(wcom,"Enter what the tree shows about the arguement")
		i=self.getInput(2)
		if i in wcom:
			writeTreeToFile(self.tree,self.ofile,result=wcom[i][0])
		else:
			print "Invalid input"
		return True

	#Writes the prompt and returns the user's input
	def getInput(self,n=1):
		sys.stdout.write(self.prompt*n+" ")
		return infun()

ifile=parser.parse_args().ifile[0]
ofile=parser.parse_args().ofile[0]
tree=TruthTree()
tree.readArguementIn(ifile)
cl=TruthtreeCommadLine(tree,ofile)
cl.makeTree()