from truthtreegen import *

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

class TotalCheckTree(TotalTruthTree):
	def __init__(self,tfname,cfname,exprnum):
		self.reader=TruthTreeReader(tfname)
		self.checkAgainstCheckFile(cfname,exprnum)
		self.top=TruthTreeCheck(total=self)
		self.setPsandC(self.reader.premises+[self.reader.conclusion],self.reader.unboundconstants)
		self.usedunboundconstants=self.reader.unboundconstantsinarguement
		for a in self.reader.factions:
			if not self.applyForwardAction(a):
				print "Incorrect Tree"
				break
		self.printCorrectness(self.reader.result)
		self.printTree()

	def checkAgainstCheckFile(self,cfname,num):
		checkreader=OffsetLogicReader(cfname,num,{"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"Atom":AtomGenTT,"FOAtom":FOAtomGenTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalGenTT,"Existential":ExistentialGenTT},self.reader.atoms,self.reader.unboundconstants)
		cexs=list(checkreader.expressions)
		ccons=list(checkreader.unboundconstants)
		for et in self.reader.premises+[self.reader.conclusion]:
			found=False
			for ec in cexs:
				if et.equals(ec):
					cexs.remove(ec)
					found=True
					break
			if not found:
				raise Exception("1 Arguements don't match")
		if len(cexs)>0:
			raise Exception("2 Arguements don't match")
		for rc in self.reader.unboundconstants:
			found=False
			for cc in ccons:
				if rc.equals(cc):
					ccons.remove(cc)
					found=True
					break
			if not found:
				raise Exception("3 Arguements don't match")
		if len(ccons)>0:
			raise Exception("4 Arguements don't match")

	def applyForwardAction(self,fa):
		if isinstance(fa,ForwardOpenLeafAction):
			return self.applyForwardOpenLeafAction(fa)
		if isinstance(fa,ForwardClosedLeafAction):
			return self.applyForwardClosedLeafAction(fa)
		if isinstance(fa,ForwardAddSplitAction):
			return self.applyForwardAddSplitAction(fa)

	def applyForwardOpenLeafAction(self,fa):
		l=self.top.getTreeSection(fa.tree)
		if l==None:
			return False
		if not l.openLeaf():
			return False
		l.open=True
		l.opnum=gopnum[0]
		gopnum[0]+=1
		if l.opnum!=fa.opnum:
			return False
		return True

	def applyForwardClosedLeafAction(self,fa):
		l=self.top.getTreeSection(fa.tree)
		if l==None:
			return False
		if not l.closedLeaf():
			return False
		l.closed=True
		l.opnum=gopnum[0]
		gopnum[0]+=1
		if l.opnum!=fa.opnum:
			return False
		return True

	#All that needs to be done
	def applyForwardAddSplitAction(self,fa):
		asrctree=self.top.getTreeSection(fa.srctree)
		if asrctree==None:
			return False
		asrce=fa.srce
		srce=None
		for e in asrctree.expressions:
			if e.equals(asrce) and e.canSplit():
				srce=e
				break
		if srce==None:
			return False
		try:
			adop=self.parseAddOp(fa.addop,srce)
		except Exception, e:
			return False
		sp=srce.ttevaluate(addoptions=adop)
		alldests=asrctree.getAddableLeaves()
		destdict={d:[] for d in alldests}
		toadd=[]
		if len(sp)==1:
			for e,d in fa.dests:
				dest=self.top.getTreeSection(d)
				if dest in destdict:
					destdict[dest].append(e)
				else:
					return False
			nume=len(sp[0])
			
			for k in destdict.keys():
				if len(destdict[k])!=nume:
					return False
				matched=[False]*len(destdict[k])
				for e in sp[0]:
					found=False
					for i,ne in enumerate(destdict[k]):
						if not matched[i] and e.equals(ne):
							matched[i]=True
							found=True
							break
					if not found:
						return False
				if not all(matched):
					return False
				for ne in destdict[k]:
					toadd.append((ne,k))
		elif len(sp)==2:
			for e,d in fa.dests:
				dest=self.top.getTreeSection(d[:-1])
				if dest in destdict:
					destdict[dest].append((e,d[-1]))
				else:
					return False
			nume=len(sp[0])+len(sp[1])
			toadd=[]
			for k in destdict.keys():
				if len(destdict[k])!=nume:
					return False
				rl=[('r','l'),('l','r')]
				for orientation in rl:
					matched=[False]*len(destdict[k])
					d0,d1=orientation
					for e in sp[0]:
						found=False
						for i,(ne,d) in enumerate(destdict[k]):
							if not matched[i] and e.equals(ne) and d0==d:
								matched[i]=True
								found=True
								break
						if not found:
							continue
					for e in sp[1]:
						found=False
						for i,(ne,d) in enumerate(destdict[k]):
							if not matched[i] and e.equals(ne) and d1==d:
								matched[i]=True
								found=True
								break
						if not found:
							continue
					if all(matched):
						break
				if not all(matched):
					return False
				k.addChildren()
				for ne,d in destdict[k]:
					if d=='r':
						toadd.append((ne,k.rchild))
					if d=='l':
						toadd.append((ne,k.lchild))
		else:
			return False
		for ne,t in toadd:
			ne.treesrc=t
			t.expressions.append(ne)
		op=srce.setToSplit(adop)
		if op!=fa.opnum:
			return False
		global gcheckopnum
		gcheckopnum=op+1
		return True

	def parseAddOp(self,op,e):
		if e.getOperator()==con.getUnicodeUniversalOperator():
			if len(self.usedunboundconstants)==0:
				newuc=None
				for uc in self.unboundconstants:
					if uc.name==op:
						newuc=uc
						break
				if newuc==None:
					raise Exception("Constant Doesn't exist")
				self.usedunboundconstants.append(newuc)
				return newuc
			for uc in self.usedunboundconstants:
				if uc.name==op:
					return uc
			#existing, or if none existing then unbound constant new one
		elif e.getOperator()==con.getUnicodeExistentialOperator():
			for uc in self.usedunboundconstants:
				if uc.name==op:
					raise Exception('Constant Already Used')
			newuc=None
			for uc in self.unboundconstants:
				if uc.name==op:
					newuc=uc
					break
			if newuc==None:
				raise Exception("Constant Doesn't exist")
			self.usedunboundconstants.append(newuc)
			return newuc
			#a unbound constant new one
		elif e.getOperator()==con.getUnicodeDisjunctionOperator() or (e.getOperator()==con.getUnicodeNegationOperator() and e.expr.getOperator()==con.getUnicodeConjunctionOperator()):
			if e.getOperator()==con.getUnicodeDisjunctionOperator():
				es=e.toList()
			if e.getOperator()==con.getUnicodeNegationOperator() and e.expr.getOperator()==con.getUnicodeConjunctionOperator():
				es=e.expr.toList()
			if len(es)==2:
				if op!='None':
					raise Exception('Invalid options')
				return None
			maxn=len(es)
			ns=[int(v) for v in op.split(',')]
			if len(ns)!=len(set(ns)):
				raise Exception('Too Many options')
			if any([v>=maxn or v<0 for v in ns]):
				raise Exception('Options not valid')
			return ns
		else:
			if op!="None":
				raise Exception('Invalid options')
			return None

	def printCorrectness(self,expected,verbose=True):
		if self.top.allSetToClosed():
			if expected==headers["Valid"]:
				s="Correctly Predicted to Valid"
			elif expected==headers["Invalid"]:
				s="Predicted to invalid but shows valid"
			elif expected==headers["Neither"]:
				s="Didn't know but shows valid"
		elif self.top.anySetToOpen():
			if expected==headers["Valid"]:
				s="Predicted to valid but shows invalid"
			elif expected==headers["Invalid"]:
				s="Correctly Predicted arguement to be invalid"
			elif expected==headers["Neither"]:
				s="Didn't know but shows invalid"
		else:
			if expected==headers["Valid"]:
				s="Predicted to valid but did not finish"
			elif expected==headers["Invalid"]:
				s="Predicted to invalid but did not finish"
			elif expected==headers["Neither"]:
				s="Didn't know and didn't finish"
		s="| "+s+" |"
		print "-"*len(s)
		print s
		print "-"*len(s)


class TruthTreeCheck(TruthTreeGen):
	def addUnboundConstants(self,ucon,ten=False):
		pass

	def getAddableLeaves(self):
		if self.isLeaf():
			if not self.open and not self.closed:
				return [self]
			return []
		return self.rchild.getAddableLeaves()+self.lchild.getAddableLeaves()

	def addChildren(self):
		self.rchild=TruthTreeCheck(self)
		self.lchild=TruthTreeCheck(self)

	def automaticAdd(self):
		return False

	def closedLeaf(self,ten=False):
		if not self.isLeaf():
			return False
		atomsinbranch=[]
		currbranch=self
		while True:
			es=currbranch.expressions
			for e in es:
				if e.isAtom():
					for a in atomsinbranch:
						if self.isContradiction(e,a):
							return True
					atomsinbranch.append(e)
			currbranch=currbranch.parent
			if currbranch==None:
				break
		return False

	def openLeaf(self,ten=False):
		if not self.isLeaf():
			return False
		if self.closedLeaf(ten):
			return False
		if self.open:
			return True
		currbranch=self
		while True:
			es=currbranch.expressions
			for e in es:
				if e.canSplit(ten):
					return False
			currbranch=currbranch.parent
			if currbranch==None:
				break
		return True

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
headers={"Valid":"V","Invalid":"I","Neither":"N","Premises":"P","Conclusion":"C","Actions":"A"}
class TruthTreeReader(LogicReader):
	def __init__(self,fname):
		self.atoms=[]
		self.unboundconstants=[]
		self.unboundconstantsinarguement=[]
		self.boundencounetered=[]
		self.constructors={"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"Atom":AtomGenTT,"FOAtom":FOAtomGenTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalGenTT,"Existential":ExistentialGenTT}
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
