from truthtreegen import *


#These are the actions are made when an action file is read
#They can be applied to a tree to replicate the actoin
#These store strings that can be deciphered to tree objects,
#They store actual expression objects though
class ForwardAddSplitAction:
	def __init__(self,srctree,srce,dests,n,addop):
		self.srctree=srctree
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
		self.top=TruthTreeCheck()
		self.setPsandC(self.reader.premises+[self.reader.conclusion],self.reader.unboundconstants)

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
				print et.toString()
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


class TruthTreeCheck(TruthTreeGen):
	pass

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
		self.boundencounetered=[]
		self.constructors={"Conjunction":GeneralizedConjunctionGenTT,"Negation":NegationGenTT,"Disjunction":GeneralizedDisjunctionGenTT,"Conditional":ConditionalGenTT,"Biconditional":BiconditionalGenTT,"Atom":AtomGenTT,"FOAtom":FOAtomGenTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalGenTT,"Existential":ExistentialGenTT}
		self.f=open(fname)
		self.result=self.getResult()
		self.premises=self.getPremises()
		self.conclusion=self.getConclusion()
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
