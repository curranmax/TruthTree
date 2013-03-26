from truthtree import *

class ExpressionGenTT(ExpressionTT):
	def __init__(self):
		self.opnum=0
		self.split=self.isAtom()
		self.tensplit=self.isAtom()
		self.treesrc=None

	#Splits the expression for generating trees
	#marks the number of the split as well
	def splitExpressionWithOptions(self,ten=False,addoptions=None):
		if ten:
			if self.tensplit:
				return [[]]
			self.tensplit=self.doneSplitting(ten)
			return self.ttevaluate(ten,addoptions)
		self.setOpnum()			
		if self.split:
			return [[]]
		self.split=self.doneSplitting(ten)
		return self.ttevaluate(ten,addoptions)

	def clearTenative(self):
		self.tensplit=self.isAtom()

	def canSplit(self,ten=False):
		if ten:
			return not self.tensplit
		return not self.split

	def doneSplitting(self,ten=False):
		return True

	def setOpnum(self):
		global gopnum
		self.opnum=gopnum
		gopnum+=1

	def getPossibleSplits(self,ten=False):
		return [None]

	def generateVersion(self):
		return False

class NegationGenTT(NegationTT,ExpressionGenTT):
	def __init__(self,ex):
		NegationTT.__init__(self,ex)
		ExpressionGenTT.__init__(self)

	#Returns the split of the expression
	#For the Negation, it matters on what the subexpression is
	def ttevaluate(self,ten=False,addoptions=None):
		if self.isAtom():
			return [([[self]],None)]
		else:
			if self.expr.getOperator()==operators['Conjunction']:
				if self.expr.isGeneralized():
					if len(self.expr.exs)==2:
						return [[NegationGenTT(self.expr.exs[0])],[NegationGenTT(self.expr.exs[1])]]
					else:
						if addoptions==None or len(addoptions)==0 or len(addoptions)==len(self.expr.exs):
							raise Exception('Need addtional option needed')
						else:
							llist=[self.expr.exs[i] for i in addoptions]
							rlist=[self.expr.exs[i] for i in range(len(self.expr.exs)) if not(i in addoptions)]
							if len(llist)>1:
								lr=[NegationGenTT(GeneralizedConjunctionGenTT(llist))]
							else:
								lr=[NegationGenTT(llist[0])]
							if len(rlist)>1:
								rr=[NegationGenTT(GeneralizedConjunctionGenTT(rlist))]
							else:
								rr=[NegationGenTT(rlist[0])]
							return [lr,rr]
				else:
					return [[NegationGenTT(self.expr.expr1)],[NegationGenTT(self.expr.expr2)]]

			elif self.expr.getOperator()==operators['Disjunction']:
				if self.expr.isGeneralized():
					return [[NegationGenTT(e) for e in self.expr.exs]]
				else:
					return [[NegationGenTT(self.expr.ex1),NegationGenTT(self.expr.ex2)]]
			elif self.expr.getOperator()==operators['Conditional']:
				return [[self.expr.ex1,NegationGenTT(self.expr.ex2)]]
			elif self.expr.getOperator()==operators['BiConditional']:
				return [[self.expr.ex1,NegationGenTT(self.expr.ex2)],[NegationGenTT(self.expr.ex1),self.expr.ex2]]
			elif self.expr.getOperator()==operators['Negation']:
				return [[self.expr.expr]]
			elif self.expr.getOperator()==operators['Universal']:
				return [[ExistentialGenTT(NegationGenTT(self.expr.expr),self.expr.con)]]
			elif self.expr.getOperator()==operators['Existential']:
				return [[UniversalGenTT(NegationGenTT(self.expr.expr),self.expr.con)]]

	def getPossibleSplits(self,ten=False):
		if self.expr.getOperator()==operators['Conjunction'] and self.expr.isGeneralized() and len(self.expr.exs)>2:
			return [[i] for i in range(len(self.expr.exs))]
		return [None]

class ConjunctionGenTT(ConjunctionTT,ExpressionGenTT):
	def __init__(self,ex1,ex2):
		ConjunctionTT.__init__(self,ex1,ex2)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[self.expr1,self.expr2]]

class GeneralizedConjunctionGenTT(GeneralizedConjunctionTT,ExpressionGenTT):
	def __init__(self,exs):
		GeneralizedConjunctionTT.__init__(self,exs)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [list(self.exs)]

class DisjunctionGenTT(DisjunctionTT,ExpressionGenTT):
	def __init__(self,ex1,ex2):
		DisjunctionTT.__init__(self,ex1,ex2)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[self.ex1],[self.ex2]]

class GeneralizedDisjunctionGenTT(GeneralizedDisjunctionTT,ExpressionGenTT):
	def __init__(self,exs):
		GeneralizedDisjunctionTT.__init__(self,exs)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		if len(self.exs)==2:
			return [[self.exs[0]],[self.exs[1]]]
		else:
			if addoptions==None or len(addoptions)==0 or len(addoptions)==len(self.exs):
				raise Exception('Additional Options Needed')
			else:
				llist=[self.exs[i] for i in addoptions]
				rlist=[self.exs[i] for i in range(len(self.exs)) if not(i in addoptions)]
				if len(llist)>1:
					lr=[GeneralizedDisjunctionGenTT(llist)]
				else:
					lr=llist
				if len(rlist)>1:
					rr=[GeneralizedDisjunctionGenTT(rlist)]
				else:
					rr=rlist
				return [lr,rr]

	def getPossibleSplits(self,ten=False):
		if len(self.exs)==2:
			return [None]
		return [[i] for i in range(len(self.exs))]

class ConditionalGenTT(ConditionalTT,ExpressionGenTT):
	def __init__(self,ex1,ex2):
		ConditionalTT.__init__(self,ex1,ex2)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[NegationGenTT(self.ex1)],[self.ex2]]

class BiconditionalGenTT(BiconditionalTT,ExpressionGenTT):
	def __init__(self,ex1,ex2):
		BiconditionalTT.__init__(self,ex1,ex2)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[self.ex1,self.ex2],[NegationGenTT(self.ex1),NegationGenTT(self.ex2)]]

class UniversalGenTT(UniversalTT,ExpressionGenTT):
	def __init__(self,ex,bcon):
		UniversalTT.__init__(self,ex,bcon)
		ExpressionGenTT.__init__(self)
		self.usedcons=[]
		self.opnums=[]
		self.tencons=[]

	def ttevaluate(self,ten=False,addoptions=None):
		t=self.treesrc.getTotal()
		if ten:
			self.tencons.append(addoptions)
			if len(t.tenunboundconstants+t.unboundconstants)==0:
				self.treesrc.addUnboundConstants(addoptions,ten)
		else:
			self.usedcons.append(addoptions)
			if len(t.unboundconstants)==0:
				self.treesrc.addUnboundConstants(addoptions,ten)
		return [[self.replaceBound(addoptions)]]

	def doneSplitting(self,ten=False):
		uc=list(self.usedcons)
		if len(self.usedcons)==0:
			return False
		if ten:
			uc+=self.tencons
		pc=self.treesrc.getUnboundConstants()
		if len(uc)==1 and len(pc)==0:
			return True
		if len(uc)!=len(pc):
			return False
		matches=[0]*len(uc)
		for u in uc:
			for i,p in enumerate(pc):
				if u.equals(p):
					matches[i]+=1
		if matches!=[1]*len(uc):
			return False
		return True

	def canSplit(self,ten=False):
		return not self.doneSplitting(ten)

	def clearTenative(self):
		self.tensplit=self.isAtom()
		self.tencons=[]

	def setOpnum(self):
		global gopnum
		self.opnums.append(gopnum)
		gopnum+=1

	def getPossibleSplits(self,ten=False):
		cons=self.treesrc.getUnboundConstants(self)
		if len(cons)==0 and ((not ten and len(self.usedcons)==0) or (ten and len(self.usedcons+self.tencons)==0)):
			return [self.treesrc.getNewUnboundConstant(ten)]
		rcons=[]
		ucons=list(self.usedcons)
		if ten:
			ucons+=self.tencons
		for c in cons:
			found=False
			for uc in ucons:
				if c.equals(uc):
					found=True
					break
			if not found:
				rcons.append(c)
		return rcons

class ExistentialGenTT(ExistentialTT,ExpressionGenTT):
	def __init__(self,ex,bcon):
		ExistentialTT.__init__(self,ex,bcon)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		t=self.treesrc.getTotal()
		if ten:
			self.treesrc.addUnboundConstants(addoptions,ten)
		else:
			self.treesrc.addUnboundConstants(addoptions,ten)
		return [[self.replaceBound(addoptions)]]

	def getPossibleSplits(self,ten=False):
		return [self.treesrc.getNewUnboundConstant(ten)]

class AtomGenTT(AtomTT,ExpressionGenTT):
	def __init__(self,name):
		AtomTT.__init__(self,name)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[self]]

class FOAtomGenTT(FOAtomTT,ExpressionGenTT):
	def __init__(self,atom,cons):
		FOAtomTT.__init__(self,atom,cons)
		ExpressionGenTT.__init__(self)

	def ttevaluate(self,ten=False,addoptions=None):
		return [[self]]


class TotalTruthTree:
	def __init__(self,fname=None,maxiters=100):
		self.maxiters=maxiters
		self.top=TruthTreeGen(maxiters=self.maxiters)
		self.top.total=self
		if fname!=None:
			self.top.readArguementIn(fname)
		self.unboundconstants=[]
		self.tenunboundconstants=[]
		self.infinite=False
		
	def run(self):
		global gopnum
		gopnum=1
		self.top.run()

	def printTree(self):
		printTruthTree(self.top)

	def writeTree(self,ofname):
		writeTreeToFile(self.top,ofname)

	def setPsandC(self,es,cons):
		for e in es:
			e.treesrc=self.top
		self.top.premises=list(es[:-1])
		self.top.conclusion=es[-1]
		self.top.expressions=list(es[:-1])
		self.top.expressions.append(NegationGenTT(es[-1]))
		self.unboundconstants=list(cons)

	def printValidity(self,i=""):
		if self.infinite:
			print i,"Too many steps taken so stopped"
		if self.top.allSetToClosed():
			print i,"Valid Arguement"
		if self.top.anySetToOpen():
			print i,"Invalid Arguement"

class TruthTreeGen(TruthTree):
	def __init__(self,parent=None,ten=False,total=None,maxiters=100):
		TruthTree.__init__(self,parent,ten)
		self.total=total
		self.maxiters=maxiters

	def run(self):
		for i in range(self.maxiters):
			if self.allClosed():
				return
			if self.anyOpen():
				return
			possplits=self.getPossibleSplits() # list of triples (expr,tree,options)
			if len(possplits)==0:
				return
			(e,src,addop)=self.findBestSplit(possplits)
			dest=src.addSplit(e.splitExpressionWithOptions(ten=False,addoptions=addop))
			self.actions.append(AddSplitAction(src,e,dest,addop))
		self.total.infinite=True

	def allClosed(self,ten=False):
		if self.closed:
			return True
		if not self.isLeaf():
			r=self.rchild.allClosed(ten) and self.lchild.allClosed(ten)
			if not ten:
				self.closed=r
			return r
		r=self.closedLeaf(ten)
		if not ten:
			self.closed=r
		return r

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

	def readArguementIn(self,fname):
		lr=LogicReader(fname,{"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"Atom":AtomGenTT,"FOAtom":FOAtomGenTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalGenTT,"Existential":ExistentialGenTT})
		self.atoms=lr.atoms
		self.premises=lr.expressions[:-1]
		self.conclusion=lr.expressions[-1]
		for p in self.premises:
			p.treesrc=self
			self.expressions.append(p)
		c=NegationGenTT(self.conclusion)
		c.treesrc=self
		self.expressions.append(c)

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

	def isContradiction(self,a1,a2):
		if not(a1.isAtom() and a2.isAtom()):
			return False
		a1op=a1.getOperator()
		a2op=a2.getOperator()
		if a1op==a2op:
			return False
		if a1op==operators['Negation']:
			return a1.expr.equals(a2)
		else:
			return a1.equals(a2.expr)

	def addChildren(self,ten=False):
		self.rchild=TruthTreeGen(self,ten)
		self.lchild=TruthTreeGen(self,ten)

	def getPossibleSplits(self):
		if self.closed or self.open:
			return []
		possplits=[(e,self,addop) for e in self.expressions for addop in e.getPossibleSplits() if e.canSplit()]
		if not self.isLeaf():
			possplits+=self.rchild.getPossibleSplits()+self.lchild.getPossibleSplits()
		return possplits

	def findBestSplit(self,possplits):
		bestchoices=[]
		universalbestchoices=[]
		bestlens=[]
		bestv=None
		universalbestv=None
		for (ps,src,addop) in possplits:
			nes=ps.splitExpressionWithOptions(ten=True,addoptions=addop)
			src.addSplit(nes,True)
			v=self.countLeafsAndTotal()
			if self.anyOpen(True):
				self.clearTenative()
				return (ps,src,addop)
			if self.allClosed(True):
				self.clearTenative()
				return (ps,src,addop)
			self.clearTenative()
			if ps.getOperator()!=operators['Universal']:
				if bestv==None:
					bestv=v
					bestchoices.append((ps,src,addop))
					bestlens.append(len(nes))
				else:
					if v==bestv:
						bestv=v
						bestchoices.append((ps,src,addop))
						bestlens.append(len(nes))
					if v<bestv:
						bestv=v
						bestchoices=[(ps,src,addop)]
						bestlens=[len(nes)]
			else:
				if universalbestv==None:
					universalbestv=v
					universalbestchoices.append((ps,src,addop))
				else:
					if v==universalbestv:
						universalbestv=v
						universalbestchoices.append((ps,src,addop))
					if v<universalbestv:
						universalbestv=v
						universalbestchoices=[(ps,src,addop)]
		if len(bestchoices)>0:
			for (ps,src,addop) in bestchoices:
				if ps.getOperator()==operators['Existential']:
					return (ps,src,addop)
			for i,(ps,src,addop) in enumerate(bestchoices):
				if bestlens[i]==1:
					return (ps,src,addop)
			return bestchoices[0]
		#Only ever split universals when there is nothing left
		else:
			mincons=min([len(ps.usedcons) for (ps,src,addop) in universalbestchoices])
			return [(ps,src,addop) for (ps,src,addop) in universalbestchoices if len(ps.usedcons)==mincons][0]


	def getTotal(self):
		p=self
		while p.parent!=None:
			p=p.parent
		return p.total

	def addUnboundConstants(self,ucon,ten=False):
		t=self.getTotal()
		if ten:
			t.tenunboundconstants.append(ucon)
		else:
			t.unboundconstants.append(ucon)

	def getNewUnboundConstant(self,ten=False):
		t=self.getTotal()
		existingucons=list(t.unboundconstants)
		if ten:
			existingucons+=list(t.tenunboundconstants)
		defaultname='a'
		while True:
			found=False
			for uc in existingucons:
				if uc.name==defaultname:
					found=True
			if not found:
				return UnBoundConstant(defaultname)
			defaultname=chr(ord(defaultname)+1)

	def clearTenative(self):
		self.getTotal().tenunboundconstants=[]
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

	def getUnboundConstants(self,up=True,down=True):
		ubc=[]
		if self.parent!=None and up:
			ubc+=self.parent.getUnboundConstants(True,False)
		if not self.isLeaf() and down:
			ubc+=self.rchild.getUnboundConstants(False,True)+self.lchild.getUnboundConstants(False,True)
		for e in self.expressions:
			ubc+=e.getUnboundConstants()
		return list(set(ubc))

cop.cons={"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"FOAtom":FOAtomGenTT,"Universal":UniversalGenTT,"Existential":ExistentialGenTT}