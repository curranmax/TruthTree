from logicdefintions import *
import argparse
from iologic import *

#This is the file which actually has the truth tree
#It also has methods to print a tree to command line and write a tree to an action file, and read an action file
#It also has special versions of the expressions, and the action objects

#Right now all of the functionaly is mixed in, but we should probably separate methods that deal with generation and checking so that someone can't manipulate the tree on their own

#You will see an input paramter ten a lot.  It stands for tenative, and when true the operation is used in part of finding the best expression to split.  This should eventually be expanded to be a number so that we can have multiple steps of prediction

checkchar=u"\u2713 "
operators=con.getUnicodeOperators()
gopnum=1
gcheckopnum=1
debug=False

#Parent of all the other TT expressions
#This has methods for automatically splitting an expression, and letting a user split a function
class ExpressionTT:
	def __init__(self):
		self.opnum=0
		self.split=self.isAtom()
		self.tensplit=self.isAtom()

	#Splits the expressoin for generating trees
	#marks the number of the split as well
	def splitExpression(self,ten=False):
		if ten:
			if self.tensplit:
				return [[]]
			self.tensplit=True
			return self.ttevaluate()
		global gopnum
		self.opnum=gopnum
		gopnum+=1
		if self.split:
			return [[]]
		self.split=True
		return self.ttevaluate()

	def clearTenative(self):
		self.tensplit=self.isAtom()

	def canSplit(self,ten=False):
		if ten:
			return not self.tensplit
		return not self.split

	def userSplit(self):
		if self.split:
			return False
		global gopnum
		self.opnum=gopnum
		gopnum+=1
		self.split=True
		return True

#***********IMPORTANT******************
#So the format of a split is a little weird
#It is a list of list of expressions
#The outer list is of length 0,1, or 2
#if it is 0 then it was an atom and shouldn't be split
#if it is len 1 then all the expressions in the only list in the outer list should be added to all existing leaves that come from the section where the split orginates
#if it is len 2 then new leaves must be made
#The limitation to two leaves means that a Generalized Disjunction must be split into only two things, and not n things

#***********IMPORTANT******************
#The isAtom() function returns if it is a Truth Tree atom, meaning if it is something like P, or ~Q.  So essentially if it is a AtomTT or a NegationTT whose subexpression is an AtomTT

#I just commented up NegationTT because te others are basically the same
class NegationTT(Negation,ExpressionTT):
	def __init__(self,ex):
		Negation.__init__(self,ex)
		ExpressionTT.__init__(self)


	def isAtom(self):
		return self.expr.getOperator()==""

	#Returns the split of the expression
	#For the Negation, it matters on what the subexpression is
	def ttevaluate(self):
		if self.isAtom():
			return [[self]]
		else:
			if self.expr.getOperator()==operators['Conjunction']:
				if self.expr.isGeneralized():
					if len(self.expr.exs)==2:
						return [[NegationTT(self.expr.exs[0])],[NegationTT(self.expr.exs[1])]]
					else:
						return [[NegationTT(self.expr.exs[0])],[NegationTT(GeneralizedConjunctionTT(self.expr.exs[1:]))]]
				else:
					return [[NegationTT(self.expr.expr1)],[NegationTT(self.expr.expr2)]]

			elif self.expr.getOperator()==operators['Disjunction']:
				if self.expr.isGeneralized():
					return [[NegationTT(e) for e in self.expr.exs]]
				else:
					return [[NegationTT(self.expr.ex1),NegationTT(self.expr.ex2)]]
			elif self.expr.getOperator()==operators['Conditional']:
				return [[self.expr.ex1,NegationTT(self.expr.ex2)]]
			elif self.expr.getOperator()==operators['BiConditional']:
				return [[self.expr.ex1,NegationTT(self.expr.ex2)],[NegationTT(self.expr.ex1),self.expr.ex2]]
			elif self.expr.getOperator()==operators['Negation']:
				return [[self.expr.expr]]

	#special toString which includes check mark if the expression was split
	#This only applies when outside is True
	def toString(self,outside=False,simp=False):
		s=Negation.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class ConjunctionTT(Conjunction,ExpressionTT):
	def __init__(self,ex1,ex2):
		Conjunction.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		return [[self.expr1,self.expr2]]

	def toString(self,outside=False,simp=False):
		s=Conjunction.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

#Assumed to have two or more things
class GeneralizedConjunctionTT(GeneralizedConjunction,ExpressionTT):
	def __init__(self,exs):
		GeneralizedConjunction.__init__(self,exs)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		return [list(self.exs)]

	def toString(self,outside=False,simp=False):
		s=GeneralizedConjunction.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class DisjunctionTT(Disjunction,ExpressionTT):
	def __init__(self,ex1,ex2):
		Disjunction.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		return [[self.ex1],[self.ex2]]

	def toString(self,outside=False,simp=False):
		s=Disjunction.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

#Assumed to have two or more things
class GeneralizedDisjunctionTT(GeneralizedDisjunction,ExpressionTT):
	def __init__(self,exs):
		GeneralizedDisjunction.__init__(self,exs)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		if len(self.exs)==2:
			return [[self.exs[0]],[self.exs[1]]]
		else:
			return [[self.exs[0]],GeneralizedDisjunctionTT(self.exs[1:])]

	def toString(self,outside=False,simp=False):
		s=GeneralizedDisjunction.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class ConditionalTT(Conditional,ExpressionTT):
	def __init__(self,ex1,ex2):
		Conditional.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		return [[NegationTT(self.ex1)],[self.ex2]]

	def toString(self,outside=False,simp=False):
		s=Conditional.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class BiconditionalTT(Biconditional,ExpressionTT):
	def __init__(self,ex1,ex2):
		Biconditional.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

	def ttevaluate(self):
		return [[self.ex1,self.ex2],[NegationTT(self.ex1),NegationTT(self.ex2)]]

	def toString(self,outside=False,simp=False):
		s=Biconditional.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class AtomTT(Atom,ExpressionTT):
	def __init__(self,name):
		Atom.__init__(self,name)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return True

	def ttevaluate(self):
		return [[self]]

	def toString(self,outside=False,simp=False):
		s=Atom.toString(self)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

#These actions are created as a tree is made
#I would like to extend these to allow for undo and redo, also making a tree structure for more complex undo and redo capabilities
#These store references to the objects in question
class AddSplitAction:
	def __init__(self,srctree,srce,dests):
		self.srctree=srctree
		self.srce=srce
		#dests is a list of tuples, where the first value in the tuple is an expression and the other is a tree
		self.dests=dests

	def toString(self,simp=False):
		s="Action "+str(self.srce.opnum)+"\n"
		s+="Srctree "+self.srctree.actionString()
		s+="\nSrce "+self.srce.toString(simp=simp)
		for e,t in self.dests:
			s+="\nDtree "+t.actionString()+"\nDe "+e.toString(simp=simp)
		return s+"\n"

class ClosedLeafAction:
	def __init__(self,t):
		self.tree=t

	def toString(self,simp=False):
		s="Action "+str(self.tree.opnum)+"\n"
		s+="Closedtree "+self.tree.actionString()
		return s+"\n"

class OpenLeafAction:
	def __init__(self,t):
		self.tree=t

	def toString(self,simp=False):
		s="Action "+str(self.tree.opnum)+"\n"
		s+="Opentree "+self.tree.actionString()
		return s+"\n"	

#These are the actions are made when an action file is read
#They can be applied to a tree to replicate the actoin
#These store strings that can be deciphered to tree objects,
#They store actual expression objects though
class ForwardAddSplitAction:
	def __init__(self,srctree,srce,dests,n):
		self.srctree=srctree
		self.srce=srce
		self.dests=dests
		self.opnum=n

class ForwardClosedLeafAction:
	def __init__(self,t,n):
		self.tree=t
		self.opnum=n

class ForwardOpenLeafAction:
	def __init__(self,t,n):
		self.tree=t
		self.opnum=n

#This class does not represent the enter tree, but one section
#It has references to its parent and child
#It may be useful to change this to TruthTree section and make TruthTree a container that manages all fo the sections
class TruthTree:
	def __init__(self,parent=None,ten=False):
		#The atoms used in the expressions
		self.atoms=[]
		#The expressions in this section
		self.expressions=[]
		#Any tenative expressions in the section
		self.tenativeExpressions=[]
		#If the section is tenative
		self.tenativeBranch=ten
		#premises and conclusion, these are only stored in the root
		self.premises=None
		self.conclusion=None
		#parent of the tree,is None if it is the root
		self.parent=parent
		#Children, assume that both are None or neither are None
		self.rchild=None
		self.lchild=None
		#open is True if all reachable expressions have been split or are atoms, or at least one child is open
		self.open=False
		#closed is True if there is a contradiction among the reachable expressions, or all children are closed
		self.closed=False
		#*******Importnant*********
		#Both open and closed cannot be true, but they can both be False.  if they are both false then the section is still being worked on

		#The number when the leaf is set to open or closed
		#This should only be non-zero in leave sections
		self.opnum=0
		#Actions, these are only stored in the root
		self.actions=[]

	#checks if all of this sections leaves are closed
	#Actually checks if leaves are closed, this is not desired during IO or when a user is making a tree
	def allClosed(self,tenative=False):
		if self.closed:
			return True
		if not self.closed and not self.isLeaf():
			r=self.rchild.allClosed(tenative) and self.lchild.allClosed(tenative)
			if not tenative:
				self.closed=r
			return r
		r=self.closedLeaf(tenative)
		if not tenative:
			self.closed=r
		return r
	
	#Doesn't calculate if closed, just if the closed variable is true for all leaves
	#use this when doing IO, or user make trees
	def allSetToClosed(self):
		if not self.closed and not self.isLeaf():
			self.closed=self.rchild.allSetToClosed() and self.lchild.allSetToClosed()
		return self.closed

	#Sets a section to closed
	#This is used when a user is making a tree
	def setClosed(self):
		global gopnum
		self.addActionToTop(ClosedLeafAction(self))
		self.closed=True
		self.opnum=gopnum
		gopnum+=1

	#Mimick the closed functions
	def anyOpen(self,ten=False):
		if self.open:
			return True
		if not self.open and self.rchild!=None and self.lchild!=None:
			r=self.rchild.anyOpen(ten) or self.lchild.anyOpen(ten)
			if not ten:
				self.open=r
			return r
		r=self.openLeaf(ten)
		if not ten:
			self.open=r
		return r

	def anySetToOpen(self):
		if not self.open and not self.isLeaf():
			self.open=self.rchild.anySetToOpen() or self.lchild.anySetToOpen()
		return self.open

	def setOpen(self):
		global gopnum
		self.addActionToTop(OpenLeafAction(self))
		self.open=True
		self.opnum=gopnum
		gopnum+=1

	#Reads in an arguement file and sets upt eh expressions correctly
	def readArguementIn(self,fname):
		lr=LogicReader(fname,{"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT})
		self.atoms=lr.atoms
		self.premises=lr.expressions[:-1]
		self.conclusion=lr.expressions[-1]
		for p in self.premises:
			self.expressions.append(p)
		self.expressions.append(NegationTT(self.conclusion))

	#checks if leaf
	#I probably should use this more, but I do manual checks everywhere which is bad
	def isLeaf(self):
		return self.rchild==None and self.lchild==None

	#Adds empty children to the tree section
	def addChildren(self,ten=False):
		self.rchild=TruthTree(self,ten)
		self.lchild=TruthTree(self,ten)

	#Adds an action to the root of a tree
	def addActionToTop(self,a):
		if self.parent==None:
			self.actions.append(a)
		else:
			self.parent.addActionToTop(a)

	#Checks if a leaf is closed
	#Used in generation, since it actually checks for contradiction
	def closedLeaf(self,ten=False):
		global gopnum
		if not self.isLeaf():
			return False

		if self.closed:
			return True
		atomsinbranch=[]
		currbranch=self
		while True:
			if ten:
				es=currbranch.expressions+currbranch.tenativeExpressions
			else:
				es=currbranch.expressions
			for e in es:
				if e.isAtom():
					for a in atomsinbranch:
						if self.isContradiction(e,a):
							if not ten:
								if self.opnum==0:
									self.opnum=gopnum
									gopnum+=1
								self.addActionToTop(ClosedLeafAction(self))
								self.closed=True
							return True
					atomsinbranch.append(e)
			currbranch=currbranch.parent
			if currbranch==None:
				break
		if not ten:
			self.closed=False
		return False

	#Same as above function but with open
	#Also this calls the above function
	def openLeaf(self,ten=False):
		global gopnum
		if not self.isLeaf():
			return False

		if self.closedLeaf(ten):
			if not ten:
				self.open=False
			return False

		if self.open:
			return True

		currbranch=self
		while True:
			if ten:
				es=currbranch.expressions+currbranch.tenativeExpressions
			else:
				es=currbranch.expressions
			for e in es:
				if e.canSplit(ten):
					if not ten:
						self.open=False
					return False
			currbranch=currbranch.parent
			if currbranch==None:
				break
		if not ten:
			if(self.opnum==0):
				self.opnum=gopnum
				gopnum+=1
			self.addActionToTop(OpenLeafAction(self))
			self.open=True
		return True

	#Checks if two truth tree atoms are contradictions
	def isContradiction(self,a1,a2):
		if not(a1.isAtom() and a2.isAtom()):
			return False
		a1op=a1.getOperator()
		a2op=a2.getOperator()
		if a1op==a2op:
			return False
		if a1op==operators['Negation']:
			return a1.expr==a2
		else:
			return a1==a2.expr

	#Gets the upper bound on size on printing a tree
	#Used when printing the tree to command line
	def getToStringSize(self):
		size=0 # Padded by spaces
		for e in self.expressions:
			size=max(size,len(" "+e.toString(True)+" "))
		if self.closed and self.isLeaf():
			size=max(size,len(" X "+str(self.opnum)+" "))
		if self.open and self.isLeaf():
			size=max(size,len(" O "+str(self.opnum)+" "))
		rsize=0
		lsize=0
		if self.rchild!=None:
			rsize=self.rchild.getToStringSize()
		if self.lchild!=None:
			lsize=self.lchild.getToStringSize()
		size=max(size,rsize+lsize)
		return size

	#Figures out the number of lines to print
	#This includes slashes to indicate parent child relationships and X's and O's to indicate close or open
	def getNumLines(self):
		size=len(self.expressions)
		if self.closed and self.isLeaf():
			size+=1
		if self.open and self.isLeaf():
			size+=1
		rsize=0
		lsize=0
		if self.rchild!=None:
			size+=1
			rsize=self.rchild.getNumLines()
		if self.lchild!=None:
			lsize=self.lchild.getNumLines()
		return size+max(rsize,lsize)

	#Gets a single line(in the form of list of strings), if that is too large then it adds its two children at that line
	def getLine(self,n):
		if n==len(self.expressions) and not self.isLeaf():
			return [[' / '],[' \\ ']]
		if n==len(self.expressions) and self.closed and self.isLeaf():
			return [" X "+str(self.opnum)+" "]
		if n==len(self.expressions) and self.open and self.isLeaf():
			return [" O "+str(self.opnum)+" "]
		if n>=len(self.expressions)+1:
			if self.rchild!=None and self.lchild!=None:
				return [self.rchild.getLine(n-len(self.expressions)-1),self.lchild.getLine(n-len(self.expressions)-1)]
			return []
		s=[]
		size=self.getToStringSize()
		if n>=len(self.expressions):
			return ""
		e=self.expressions[n]
		rs=size/2-len(e.toString(True))/2
		ls=size-rs-len(e.toString(True))
		s.append(" "*rs+e.toString(True)+" "*ls)
		return s

	#Produces a nested list of the sizes of lines.  This is used to leave space for sections that finished, but there is still other stuff on the right and left of it
	def getLineSize(self,n):
		if n==len(self.expressions) and not self.isLeaf():
			return [[self.rchild.getToStringSize()],[self.lchild.getToStringSize()]]
		if n==len(self.expressions) and self.closed and self.isLeaf():
			return [len(" X "+str(self.opnum)+" ")]
		if n==len(self.expressions) and self.open and self.isLeaf():
			return [len(" O "+str(self.opnum)+" ")]
		if n>=len(self.expressions)+1:
			if self.rchild!=None and self.lchild!=None:
				return [self.rchild.getLineSize(n-len(self.expressions)-1),self.lchild.getLineSize(n-len(self.expressions)-1)]
		return [self.getToStringSize()]

	#Used to translate a tree section into a string that can be written to an action file and the used to get the tree section back
	#Format: 'hrlrl..rl' the first character is an h (indicating head),followed by r and l, where r means rchild and l means lchild
	def actionString(self,c=None):
		if self.parent==None:
			if self.isLeaf():
				return "h"
			if c==self.rchild:
				return "hr"
			if c==self.lchild:
				return "hl"
			return "h"
		if c==None:
			return self.parent.actionString(self)
		if c==self.rchild:
			return self.parent.actionString(self)+"r"
		if c==self.lchild:
			return self.parent.actionString(self)+"l"

	#Takes a list of list of expressions and adds that split
	def addSplit(self,nes,ten=False):
		#If this is a closed leaf, then nothing happens
		#If the leaf is open, then no splits should have possible to make anyway
		if self.closedLeaf(ten):
			#The return is a list of the tree sections which added any expressions
			return []
		if len(nes)==1:
			#Addes the expressions to a leave
			if self.isLeaf():
				d=[]
				if ten:
					for e in nes[0]:
						self.tenativeExpressions.append(e)
				else:
					for e in nes[0]:
						self.expressions.append(e)
						d.append((e,self))
				return d
			else:
				#Otherwise the expressions must be added to both children
				#The copying gets rid of any weird things, but the special funtion is used to ensure that all AtomTT's are still consistent
				d1=self.rchild.addSplit(copyListOfExpressions(nes),ten)
				d2=self.lchild.addSplit(copyListOfExpressions(nes),ten)
				if not ten:
					return d1+d2
		#Same but when child treees must be made
		if len(nes)==2:
			if self.rchild==None and self.lchild==None:
				self.addChildren(ten)
				d1=self.rchild.addSplit([nes[0]],ten)
				d2=self.lchild.addSplit([nes[1]],ten)
			else:
				d1=self.rchild.addSplit(copyListOfExpressions(nes),ten)
				d2=self.lchild.addSplit(copyListOfExpressions(nes),ten)
			if not ten:
				return d1+d2

	#gets all expressions that can be split and the tree sections they are in
	def getPossibleSplits(self):
		if self.closed or self.open:
			return []
		possplits=[(e,self) for e in self.expressions if e.canSplit()]
		if self.rchild!=None:
			possplits+=self.rchild.getPossibleSplits()+self.lchild.getPossibleSplits()
		return possplits

	#Returns a list of all Truth Tree atoms that are reachable form a tree section
	def getAllReachableAtoms(self):
		atoms=[e for e in self.expressions if e.isAtom()]
		if self.parent!=None:
			atoms+=self.parent.getAllReachableAtoms()
		return atoms

	#Gets statistics of the tree as a whole, used to determine the best split so always uses tenative data
	def countLeafsAndTotal(self):
		if self.isLeaf():
			if not self.closedLeaf(True) and not self.openLeaf(True):
				return (1,1,1)
			return (0,1,1)
		else:
			ru,rl,rt=self.rchild.countLeafsAndTotal()
			lu,ll,lt=self.lchild.countLeafsAndTotal()
			return (ru+lu,rl+ll,rt+lt+1)

	#Gets rid of any tenative data so another expression can be tried
	def clearTenative(self):
		for e in self.expressions:
			e.clearTenative()
		self.tenativeExpressions=[]
		if self.rchild!=None:
			self.rchild.clearTenative()
			if self.rchild.tenativeBranch:
				self.rchild=None
		if self.lchild!=None:
			self.lchild.clearTenative()
			if self.lchild.tenativeBranch:
				self.lchild=None

	#Finds the "best" expression to split
	def findBestSplit(self,possplits):
		bestchoices=[]
		bestv=None
		for (ps,src) in possplits:
			src.addSplit(ps.splitExpression(True),True)
			v=self.countLeafsAndTotal()
			if self.anyOpen(True):
				self.clearTenative()
				return (ps,src)
			if self.allClosed(True):
				self.clearTenative()
				return (ps,src)
			self.clearTenative()
			if bestv==None:
				bestv=v
				bestchoices.append((ps,src))
			else:
				if v==bestv:
					bestv=v
					bestchoices.append((ps,src))
				if v<bestv:
					bestv=v
					bestchoices=[(ps,src)]
		for (ps,src) in bestchoices:
			if len(ps.ttevaluate())==1:
				return (ps,src)
		return bestchoices[0]

	#Generates the tree
	def run(self):
		while True:
			if self.allClosed():
				return
			if self.anyOpen():
				return
			possplits=self.getPossibleSplits()
			if len(possplits)==0:
				return
			(e,src)=self.findBestSplit(possplits)
			dest=src.addSplit(e.splitExpression())
			self.actions.append(AddSplitAction(src,e,dest))
		
	#Used by the checker to set up the tree	
	def initialize(self,a,p,c):
		self.atoms=a
		self.premises=p
		self.conclusion=c
		for pr in self.premises:
			self.expressions.append(pr)
		self.expressions.append(NegationTT(self.conclusion))

	#Applies a forward action, calls a more specific function based on the type of forward action
	def applyForwardAction(self,fa):
		global gcheckopnum
		if fa.opnum!=gcheckopnum:
			return False
		if isinstance(fa,ForwardAddSplitAction):
			r=self.applyForwardAddSplitAction(fa)
		elif isinstance(fa,ForwardClosedLeafAction):
			r=self.applyForwardClosedLeafAction(fa)
		elif isinstance(fa,ForwardOpenLeafAction):
			r=self.applyForwardOpenLeafAction(fa)
		gcheckopnum+=1
		return r

	#Applies a split
	#THERE ARE BUGS IN THIS
	#Example:  the checker won't recognize splitting A&A into A and A as valid.  This is because the two results equal each other
	#Also won't work with Generalized Disjunctions, because the code thinks the only split is the first expression and the rest in two branches
	def applyForwardAddSplitAction(self,fa):
		#Gets the src tree and expression nd makes sure things are good
		global gcheckopnum
		stree=self.getTreeSection(fa.srctree)
		if stree==None:
			return False
		actuale=None
		for e in stree.expressions:
			if e.equals(fa.srce):
				actuale=e
				break
		if actuale==None:
			return False
		#Gets the theorical split, for Generalized Disjunctions this won't be right
		nes=actuale.splitExpression()
		#Finds all the spots where the split should be, this doesn't include the making of branches, since those would just be taking all of those spots and taking the rchild and lchild of those
		#These are also tree objects
		aspots=self.getAllAddSpots(fa.srctree,stree)
		if not len(nes) in [1,2]:
			return False
		#Case that no new branches need to be made
		if len(nes)==1:
			#Makes sure there is a one to one between (expr, tree) in the action and in theory
			es=nes[0]
			if len(es)*len(aspots)!=len(fa.dests):
				return False
			necount=[0]*len(es)
			spotslist=[0]*len(aspots)
			for e,t in fa.dests:
				for i,ne in enumerate(es):
					if e.equals(ne):
						necount[i]+=1
				for i,sp in enumerate(aspots):
					if t==sp:
						spotslist[i]+=1
			for nec in necount:
				if nec!=len(aspots):
					return False
			for spn in spotslist:
				if spn!=len(es):
					return False
			for sp in aspots:
				t=self.getTreeSection(sp)
				if t==None:
					return False
				t.expressions+=es
		if len(nes)==2:
			#This is pretty complicated because of the ambiguity of where the user can put expressions, but basically
			#for each possible spot in aspots
			#	There must be an one to one match in expressions in the action with aspots+'r' to those in es1
			#   and There must be an one to one match in expressions in the action with aspots+'l' to those in es2
			#                 OR
			#	There must be an one to one match in expressions in the action with aspots+'r' to those in es2
			#   and There must be an one to one match in expressions in the action with aspots+'l' to those in es1
			#I check that and also record wether it was the first or the second, so I can recreate the tree accurately
			es1=nes[0]
			es2=nes[1]
			if len(es1)*len(aspots)+len(es2)*len(aspots)!=len(fa.dests):
				return False

			spotsrl=[]
			for sp in aspots:
				for erl in [["r","l"],["l","r"]]:
					w=True
					m1=[0]*len(es1)
					m2=[0]*len(es2)
					for i,ne in enumerate(es1):
						for e,t in fa.dests:
							if ne.equals(e) and t==sp+erl[0]:
								m1[i]+=1
					for i,ne in enumerate(es2):
						for e,t in fa.dests:
							if ne.equals(e) and t==sp+erl[1]:
								m2[i]+=1
					for m in m1:
						if m!=len(es1):
							w=False
					for m in m2:
						if m!=len(es2):
							w=False
					if w:
						spotsrl.append(erl)
						break
				if not w:
					return False
			for i,sp in enumerate(aspots):
				t=self.getTreeSection(sp)
				if not t.isLeaf():
					return False
				t.addChildren()
				if spotsrl[i][0]=='r':
					t.rchild.expressions+=es1
					t.lchild.expressions+=es2
				else:
					t.rchild.expressions+=es2
					t.lchild.expressions+=es1
		return True

	#Closes the tree section specified by the forward action
	def applyForwardClosedLeafAction(self,fa):
		l=self.getTreeSection(fa.tree)
		if l==None:
			return False
		return l.closedLeaf()

	#Opens the tree section specified by the forward action
	def applyForwardOpenLeafAction(self,fa):
		l=self.getTreeSection(fa.tree)
		if l==None:
			return False
		return l.openLeaf()

	#Gets the tree section from its actionstring
	def getTreeSection(self,lstring):
		t=self
		while t.parent!=None:
			t=t.parent
		if lstring[0]!='h':
			return None
		for lr in lstring[1:]:
			if t.isLeaf():
				return None
			if lr=='r':
				t=t.rchild
			if lr=='l':
				t=t.lchild
		return t

	#Finds all spots that a split would add to
	def getAllAddSpots(self,lstring,stree):
		if stree.closed or stree.open:
			return []
		if stree.isLeaf():
			return [lstring]
		return self.getAllAddSpots(lstring+"r",stree.rchild)+self.getAllAddSpots(lstring+"l",stree.lchild)

	#Adds a split specified by the user
	def userSplit(self,sexpr,desttrees,destes):
		me=None
		for e in self.expressions:
			if sexpr.equals(e):
				me=e
				break
		if me==None:
			print "No matching expression"
			return False
		if not me.userSplit():
			print "Expression already split"
			return False
		ts=[]
		for i,dt in enumerate(desttrees):
			t=self.getTreeSection(dt)
			if t==None:
				t=self.getTreeSection(dt[:-1])
				if t==None:
					print "Invalid destination tree"
				t.addChildren()
				t=self.getTreeSection(dt)
			t.expressions.append(destes[i])
			ts.append((destes[i],t))
		if self.anyEmptySections():
			print "Empty Tree Sections"
			return False
		self.addActionToTop(AddSplitAction(self,me,ts))
		return True

	#Makes sure no empty sections were made by user adding things
	def anyEmptySections(self,s=True):
		t=self
		if s:
			while t.parent!=None:
				t=t.parent
		if len(t.expressions)==0:
			return True
		if t.isLeaf():
			return False
		return t.rchild.anyEmptySections(False) or t.lchild.anyEmptySections(False)


#Reads in an action file
#Format
#I|V|N  //I means invalid arguement, V manes valid and N means neither(I am not sure if i should get rid of this)
#P      //Premises
#expressions
#//Newline indicates end of expressions
#C      //Conclusion
#an expression
#
#A  	//Actions
#Action
#//Newline between actions
#Action
#
#...
class TruthTreeReader(LogicReader):
	def __init__(self,fname):
		self.atoms=[]
		self.constructors={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT}
		self.f=open(fname)
		self.result=self.getResult()
		self.premises=self.getPremises()
		self.conclusion=self.getConclusion()
		self.factions=self.getActions()
		self.f.close()
		self.tree=TruthTree()
		self.tree.initialize(self.atoms,self.premises,self.conclusion)
		
	def findLineWithJustHeader(self,rs):
		for line in self.f:
			for r in rs:
				if line==r+"\n":
					return r
			for k in headers.keys():
				if not(headers[k] in rs) and line==headers[k]+"\n":
					self.raiseError()
		self.raiseError()

	def getResult(self):
		rs=[headers["Valid"],headers["Invalid"],headers["Neither"]]
		return self.findLineWithJustHeader(rs)
		
	def getPremises(self):
		self.findLineWithJustHeader([headers["Premises"]])
		ps=[]
		for line in self.f:
			if line=="\n":
				return ps
			ps.append(self.findExpression(line))

	def getConclusion(self):
		self.findLineWithJustHeader([headers["Conclusion"]])
		for line in self.f:
			return self.findExpression(line)

	def getActions(self):
		self.findLineWithJustHeader([headers["Actions"]])
		ls=""
		actions=[]
		for line in self.f:
			if line=="\n":
				actions.append(self.parseAction(ls))
				ls=""
			else:
				ls+=line
		return actions

	def parseAction(self,a):
		lines=a.split()
		if len(lines)<4 or len(lines)%2!=0:
			self.raiseError()
		if lines[0]!="Action":
			self.raiseError()
		opnum=int(lines[1])
		if lines[2]=='Closedtree':
			return ForwardClosedLeafAction(lines[3],opnum)
		if lines[2]=='Opentree':
			return ForwardOpenLeafAction(lines[3],opnum)
		if lines[2]=='Srctree':
			if len(lines)<6:
				self.raiseError()
			st=lines[3]
			if lines[4]!="Srce":
				raiseError()
			se=self.findExpression(lines[5])
			if (len(lines)-6)%4!=0:
				self.raiseError()
			dest=[]
			for i in xrange(6,len(lines),4):
				if lines[i]!="Dtree":
					self.raiseError()
				t=lines[i+1]
				if lines[i+2]!='De':
					self.raiseError()
				e=self.findExpression(lines[i+3])
				dest.append((e,t))
			return ForwardAddSplitAction(st,se,dest,opnum)

	def raiseError(self):
		raise IOError('Invalid Input File')
		
#Prints the tree assuming this is the root
def printTruthTree(tree):
	if tree.parent!=None:
		print "Not root of a tree"
		return

	# if tree.anySetToOpen():
	# 	print "Open Branches"

	# if tree.allSetToClosed():
	# 	print "All Branches are Closed"

	lines=[]
	linesize=[]
	nl=tree.getNumLines()
	if nl<=0:
		print ""
		return
	for i in range(nl):
		lines.append(tree.getLine(i))
		linesize.append(tree.getLineSize(i))

	#if children are smaller than parents
	maxls=max([nestedSum(ls) for ls in linesize])	
	for i,ls in enumerate(linesize):
		ns=nestedSum(ls)
		if maxls>ns and i>=1:
			linesize[i]=lengthenLine(ls,linesize[i-1])

	s=""
	for i in range(len(lines)):
		l=processLine(lines[i],linesize[i])
		s+=l+"\n"
	print s

#Processes a single line, and alters it so it looks nice
def processLine(l,lsize):
	if len(l)==0:
		return " "*lsize[0]
	if len(l)==1:
		e=""
		for s in l[0].split():
			e+=s+" "
		e=e[:-1]		
		rs=lsize[0]/2-len(e)/2
		ls=lsize[0]-rs-len(e)
		l[0]=" "*rs+e+" "*ls
		return l[0]
	return processLine(l[0],lsize[0])+processLine(l[1],lsize[1])

def nestedSum(l):
	if len(l)==1:
		return l[0]
	return nestedSum(l[0])+nestedSum(l[1])

#lengthens a line so that everything is nice
def lengthenLine(l,newns):
	if len(l)==1:
		return [newns[0]]
	nl0=float(nestedSum(l[0]))
	nl1=float(nestedSum(l[1]))
	rw=nl0/(nl0+nl1)
	if len(newns)==1:
		return [lengthenLine(l[0],[int(newns[0]*rw)])]+[lengthenLine(l[1],[newns[0]-int(newns[0]*rw)])]
	return [lengthenLine(l[0],newns[0])]+[lengthenLine(l[1],newns[1])]

#Copies a split
def copyListOfExpressions(le):
	nl=[[copyExpression(e) for e in subl] for subl in le]
	return nl

#Copies everything but AtomTT
def copyExpression(e):
	if e.getOperator()=="":
		return e
	if e.getOperator()==operators["Negation"]:
		return NegationTT(copyExpression(e.expr))
	if e.getOperator()==operators["Conjunction"]:
		return ConjunctionTT(copyExpression(e.expr1),copyExpression(e.expr2))
	if e.getOperator()==operators["Disjunction"]:
		return DisjunctionTT(copyExpression(e.ex1),copyExpression(e.ex2))
	if e.getOperator()==operators["Conditional"]:
		return ConditionalTT(copyExpression(e.ex1),copyExpression(e.ex2))
	if e.getOperator()==operators["Biconditional"]:
		return Biconditional(copyExpression(e.ex1),copyExpression(e.ex2))

#headers for TruthTreeReader
headers={"Valid":"V","Invalid":"I","Neither":"N","Premises":"P","Conclusion":"C","Actions":"A"}

#Rights a tree to a file
def writeTreeToFile(tree,fname,append=False,result=None):
	m='w'
	if append:
		m='a'
	f=open(fname,m)
	if result==None:
		if tree.allsetToClosed():
			f.write(headers["Valid"]+"\n")
		elif tree.anysetToOpen():
			f.write(headers["Invalid"]+"\n")
		else:
			f.write(headers["Neither"]+"\n")
	else:
		f.write(headers[result]+"\n")
	f.write(headers["Premises"]+"\n")
	for p in tree.premises:
		f.write(p.toString(simp=True)+"\n")
	f.write("\n"+headers["Conclusion"]+"\n")
	f.write(tree.conclusion.toString(simp=True)+"\n")
	f.write("\n"+headers["Actions"]+"\n")
	for a in tree.actions:
		f.write(a.toString(simp=True)+"\n")
	f.close()
