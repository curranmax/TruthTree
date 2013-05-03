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
gopnum=[1]
debug=False

#Parent of all the other TT expressions
#This has methods for automatically splitting an expression, and letting a user split a function
class ExpressionTT:
	def __init__(self):
		self.opnum=0
		self.split=self.isAtom()
		self.tensplit=self.isAtom()
		self.treesrc=None

	def userSplit(self,op=None,adop=None):
		self.split=True
		opnum=self.setOpnum(op)
		if adop!=None:
			self.userAdop(adop)
		return opnum

	def userAdop(self,adop):
		pass

	def setOpnum(self,op=None):
		if op==None:
			self.opnum=gopnum[0]
			gopnum[0]+=1
		else:
			self.opnum=op
			gopnum[0]=op+1
		return self.opnum

	def needAddop(self):
		return False

	def canUserSplit(self):
		return self.opnum==0 or not self.split

	def undoSplit(self,addop,op):
		self.split=False
		gopnum[0]=op
		self.opnum=0

	def findSubstitutedConstant(self,expr):
		slist=self.toList()
		elist=expr.toList()
		if len(slist)!=len(elist) or len(slist)==0:
			return None
		sl=zip(slist,elist)
		for s,e in sl:
			t=s.findSubstitutedConstant(e)
			if t!=None:
				return t
		return None


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

	#special toString which includes check mark if the expression was split
	#This only applies when outside is True
	def toString(self,outside=False,simp=False):
		s=Negation.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

	def needAddop(self):
		if self.expr.getOperator()==operators['Conjunction'] and self.expr.isGeneralized() and len(self.expr.exs)>2:
			return True
		return False

class ConjunctionTT(Conjunction,ExpressionTT):
	def __init__(self,ex1,ex2):
		Conjunction.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

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

	def toString(self,outside=False,simp=False):
		s=GeneralizedDisjunction.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

	def needAddop(self):
		if len(self.exs)>2:
			return True
		return False

class ConditionalTT(Conditional,ExpressionTT):
	def __init__(self,ex1,ex2):
		Conditional.__init__(self,ex1,ex2)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return False

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

	def toString(self,outside=False,simp=False):
		s=Biconditional.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class UniversalTT(Universal,ExpressionTT):
	def __init__(self,ex,bcon):
		Universal.__init__(self,ex,bcon)
		ExpressionTT.__init__(self)
		self.usedcons=[]
		self.opnums=[]
		self.tencons=[]

	def isAtom(self):
		return False

	def userAdop(self,adop):
		self.usedcons.append(adop)

	def setOpnum(self,op):
		if op==None:
			op=gopnum[0]
		self.opnums.append(op)
		gopnum[0]=op+1
		return op

	def toString(self,outside=False,simp=False):
		s=Universal.toString(self,simp)
		if outside:
			for i,uc in enumerate(self.usedcons):
				s+=" "+str(self.opnums[i])+"-"+uc.toString()
		return s

	def needAddop(self):
		return True

	def canUserSplit(self):
		return True

	def undoSplit(self,addop,op):
		self.split=False
		gopnum[0]=op
		self.opnums.remove(op)
		for uc in self.usedcons:
			if uc.equals(addop):
				self.usedcons.remove(uc)
				break
		self.opnum=0

class ExistentialTT(Existential,ExpressionTT):
	def __init__(self,ex,bcon):
		Existential.__init__(self,ex,bcon)
		ExpressionTT.__init__(self)
		self.usedcon=None

	def isAtom(self):
		return False

	def userAdop(self,adop):
		self.usedcon=adop

	def toString(self,outside=False,simp=False):
		s=Existential.toString(self,simp)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)+"-"+self.usedcon.toString()
		return s

	def needAddop(self):
		return True

	def undoSplit(self,addop,op):
		self.split=False
		gopnum[0]=op
		self.opnum=0
		self.usedcon=None

class AtomTT(Atom,ExpressionTT):
	def __init__(self,name):
		Atom.__init__(self,name)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return True

	def toString(self,outside=False,simp=False):
		s=Atom.toString(self)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

class FOAtomTT(FOAtom,ExpressionTT):
	def __init__(self,atom,cons):
		FOAtom.__init__(self,atom,cons)
		ExpressionTT.__init__(self)

	def isAtom(self):
		return True

	def toString(self,outside=False,simp=False):
		s=FOAtom.toString(self)
		if self.split and self.opnum>0 and outside:
			s+=" "+checkchar+str(self.opnum)
		return s

	def findSubstitutedConstant(self,expr):
		if not isinstance(expr,FOAtomTT):
			return None
		if len(self.vs)!=len(expr.vs) or len(self.vs)==0:
			return None
		for sv,ev in zip(self.vs,expr.vs):
			if sv.isBound() and not ev.isBound():
				return ev
			if not sv.isBound() and ev.isBound():
				return sv
		return None

#These actions are created as a tree is made
#I would like to extend these to allow for undo and redo, also making a tree structure for more complex undo and redo capabilities
#These store references to the objects in question
class AddSplitAction:
	def __init__(self,srctree,srce,dests,addop,opnum):
		self.srctree=srctree
		self.srce=srce
		#dests is a list of tuples, where the first value in the tuple is an expression and the other is a tree
		self.dests=dests
		self.addop=addop
		self.opnum=opnum

	def toString(self,simp=False):
		s="Action "+str(self.opnum)+"\n"
		s+="Srctree "+self.srctree.actionString()
		s+="\nSrce "+self.srce.toString(simp=simp)
		if self.srce.getOperator() in [operators['Universal'],operators['Existential']]: 
			s+="\nSrcops "+self.addop.toString()
		elif self.addop==None:
			s+="\nSrcops None"
		else:
			s+="\nSrcops "
			for i in self.addop:
				s+=str(i)+","
			s=s[:-1]
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
	
	#Doesn't calculate if closed, just if the closed variable is true for all leaves
	#use this when doing IO, or user make trees
	def allSetToClosed(self):
		if not self.closed and not self.isLeaf():
			self.closed=self.rchild.allSetToClosed() and self.lchild.allSetToClosed()
		return self.closed

	#Sets a section to closed
	#This is used when a user is making a tree
	def setClosed(self,op=None):
		self.addActionToTop(ClosedLeafAction(self))
		self.closed=True
		if op==None:
			self.opnum=gopnum[0]
			gopnum[0]+=1
		else:
			self.opnum=op
			gopnum[0]=op+1

	def anySetToOpen(self):
		if not self.open and not self.isLeaf():
			self.open=self.rchild.anySetToOpen() or self.lchild.anySetToOpen()
		return self.open

	def setOpen(self,op=None):
		self.addActionToTop(OpenLeafAction(self))
		self.open=True
		if op==None:
			self.opnum=gopnum[0]
			gopnum[0]+=1
		else:
			self.opnum=op
			gopnum[0]=op+1
		
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
		if self.lchild!=None:
			lsize=self.lchild.getToStringSize()
		if self.rchild!=None:
			rsize=self.rchild.getToStringSize()
		size=max(size,lsize+rsize)
		return size

	#Figures out the number of lines to print
	#This includes slashes to indicate parent child relationships and X's and O's to indicate close or open
	def getNumLines(self):
		size=len(self.expressions)
		if self.closed and self.isLeaf():
			size+=1
		if self.open and self.isLeaf():
			size+=1
		lsize=0
		rsize=0
		if self.lchild!=None:
			size+=1
			lsize=self.lchild.getNumLines()
		if self.rchild!=None:
			rsize=self.rchild.getNumLines()
		
		return size+max(lsize,rsize)

	#Gets a single line(in the form of list of strings), if that is too large then it adds its two children at that line
	def getLine(self,n):
		if n==len(self.expressions) and not self.isLeaf():
			return [[' / '],[' \\ ']]
		if n==len(self.expressions) and self.closed and self.isLeaf():
			return [" X "+str(self.opnum)+" "]
		if n==len(self.expressions) and self.open and self.isLeaf():
			return [" O "+str(self.opnum)+" "]
		if n>=len(self.expressions)+1:
			if not self.isLeaf():
				return [self.lchild.getLine(n-len(self.expressions)-1),self.rchild.getLine(n-len(self.expressions)-1)]
			return []
		s=[]
		size=self.getToStringSize()
		if n>=len(self.expressions):
			return ""
		e=self.expressions[n]
		ls=size/2-len(e.toString(True))/2
		rs=size-ls-len(e.toString(True))
		s.append(" "*ls+e.toString(True)+" "*rs)
		return s

	#Produces a nested list of the sizes of lines.  This is used to leave space for sections that finished, but there is still other stuff on the right and left of it
	def getLineSize(self,n):
		if n==len(self.expressions) and not self.isLeaf():
			return [[self.lchild.getToStringSize()],[self.rchild.getToStringSize()]]
		if n==len(self.expressions) and self.closed and self.isLeaf():
			return [len(" X "+str(self.opnum)+" ")]
		if n==len(self.expressions) and self.open and self.isLeaf():
			return [len(" O "+str(self.opnum)+" ")]
		if n>=len(self.expressions)+1:
			if not self.isLeaf():
				return [self.lchild.getLineSize(n-len(self.expressions)-1),self.rchild.getLineSize(n-len(self.expressions)-1)]
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

	#Used by the checker to set up the tree	
	def initialize(self,a,p,c):
		self.atoms=a
		self.premises=p
		self.conclusion=c
		for pr in self.premises:
			self.expressions.append(pr)
		self.expressions.append(NegationTT(self.conclusion))

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
	nl=[[cop.copyExpression(e) for e in subl] for subl in le]
	return nl

cop.cons={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"FOAtom":FOAtomTT,"Universal":UniversalTT,"Existential":ExistentialTT}

#headers for TruthTreeReader
headers={"Valid":"V","Invalid":"I","Neither":"N","Premises":"P","Conclusion":"C","Actions":"A"}

#Rights a tree to a file
def writeTreeToFile(tree,fname,append=False,result=None):
	m='w'
	if append:
		m='a'
	f=open(fname,m)
	if result==None:
		if tree.allSetToClosed():
			f.write(headers["Valid"]+"\n")
		elif tree.anySetToOpen():
			f.write(headers["Invalid"]+"\n")
		else:
			f.write(headers["Neither"]+"\n")
	else:
		if len(result)>1:
			f.write(headers[result]+"\n")
		else:
			f.write(result+"\n")
	f.write(headers["Premises"]+"\n")
	for p in tree.premises:
		f.write(p.toString(simp=True)+"\n")
	f.write("\n"+headers["Conclusion"]+"\n")
	f.write(tree.conclusion.toString(simp=True)+"\n")
	f.write("\n"+headers["Actions"]+"\n")
	for a in tree.actions:
		f.write(a.toString(simp=True)+"\n")
	f.close()

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
#headers for TruthTreeReader
#These are the actions are made when an action file is read
#They can be applied to a tree to replicate the actoin
#These store strings that can be deciphered to tree objects,
#They store actual expression objects though
class ForwardAddSplitAction:
	def __init__(self,srctree,srce,dests,n,addop):
		#'hrlrlrlrlrl...'
		self.srctree=srctree
		#Expression object
		self.srce=srce
		self.dests=dests
		self.opnum=n
		self.addop=addop

class ForwardClosedLeafAction:
	def __init__(self,t,n):
		self.tree=t
		self.opnum=n

class ForwardOpenLeafAction:
	def __init__(self,t,n):
		self.tree=t
		self.opnum=n

headers={"Valid":"V","Invalid":"I","Neither":"N","Premises":"P","Conclusion":"C","Actions":"A"}
class TruthTreeReader(LogicReader):
	def __init__(self,fname,constructors=None):
		self.atoms=[]
		self.unboundconstants=[]
		self.unboundconstantsinarguement=[]
		self.boundencounetered=[]
		if constructors==None:
			self.constructors={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT,"FOAtom":FOAtomTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalTT,"Existential":ExistentialTT}
		else:
			self.constructors=constructors
		self.f=open(fname)
		self.result=self.getResult()
		self.premises=self.getPremises()
		self.conclusion=self.getConclusion()
		self.unboundconstantsinarguement=list(self.unboundconstants)
		self.factions=self.getActions()
		self.f.close()
		
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
			if len(lines)<8:
				self.raiseError()
			st=lines[3]
			if lines[4]!="Srce":
				raiseError()
			se=self.findExpression(lines[5])
			if lines[6]!="Srcops":
				raiseError()
			sops=lines[7]
			if (len(lines)-8)%4!=0:
				self.raiseError()
			dest=[]
			for i in xrange(8,len(lines),4):
				if lines[i]!="Dtree":
					self.raiseError()
				t=lines[i+1]
				if lines[i+2]!='De':
					self.raiseError()
				e=self.findExpression(lines[i+3])
				dest.append((e,t))
			return ForwardAddSplitAction(st,se,dest,opnum,sops)

	def raiseError(self):
		raise IOError('Invalid Input File')

