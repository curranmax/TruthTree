
#This started as a way to solve the problem on hw2 with the A's B's and C's and axioms which is why constants  is the way it is
#It stores the constants such as unicode of the operators and simple representation fo the operators in one central place
#I know this is not the best way to do this, but it is the way that emerged
class Constants:
	#This was specifically for the hw problem, because my intial script was wrong, so I thought I needed to expand to four values
	def __init__(self,nvals,startchar='A'):
		self.vals=[]
		for i in range(nvals):
			self.vals.append(startchar)
			startchar=chr(ord(startchar)+1)
		numpos=int(nvals+nvals*(nvals+1)/2)
		self.rs=[self.vals[0]]*(numpos)
		self.debug=False
		self.intial=True

	#Not used in the truth tree, but used in the Truth table
	def getNegationVal(self,v):
		return self.rs[self.vals.index(v)]

	def getConjunctionVal(self,v1,v2):
		i1=self.vals.index(v1)
		i2=self.vals.index(v2)
		if i1>i2:
			t=i1
			i1=i2
			i2=t
		return self.rs[len(self.vals)+i1*(i1+1)/2+i2]

	#Shorthand because the values are only stored for negation and conjunction and the others are computed using the equivalnce rules
	def getDisjunctionVal(self,v1,v2):
		return self.getNegationVal(self.getConjunctionVal(self.getNegationVal(v1),self.getNegationVal(v2)))

	#This is also for the hw
	#True if this is the last increment
	def incrementDefinedVals(self):
		for i,v in enumerate(self.rs):
			i1=self.vals.index(v)
			if i1==len(self.vals)-1:
				self.rs[i]=self.vals[0]
			else:
				self.rs[i]=self.vals[i1+1]
				return False
		return True

	#Dictionary of the unicode operators, used for outputing to the command line
	def getUnicodeOperators(self):
		return {"Negation":self.getUnicodeNegationOperator(),"Conjunction":self.getUnicodeConjunctionOperator(),"Disjunction":self.getUnicodeDisjunctionOperator(),"Conditional":self.getUnicodeConditionalOperator(),"BiConditional":self.getUnicodeBiConditionalOperator(),"Universal":self.getUnicodeUniversalOperator(),"Existential":self.getUnicodeExistentialOperator()}

	#Dictionary of the simple operators, used with the files
	def getSimpleOperators(self):
		return {"Negation":self.getSimpleNegationOperator(),"Conjunction":self.getSimpleConjunctionOperator(),"Disjunction":self.getSimpleDisjunctionOperator(),"Conditional":self.getSimpleConditionalOperator(),"BiConditional":self.getSimpleBiConditionalOperator(),"Universal":self.getSimpleUniversalOperator(),"Existential":self.getSimpleExistentialOperator()}

	#List for the logic reader
	def getSimpleUnaryOperators(self):
		return [self.getSimpleNegationOperator(),self.getSimpleUniversalOperator(),self.getSimpleExistentialOperator()]

	def getSimpleBinaryOperators(self):
		return [self.getSimpleConjunctionOperator(),self.getSimpleDisjunctionOperator(),self.getSimpleConditionalOperator(),self.getSimpleBiConditionalOperator()]

	#Actual values for the operators
	#Stored here, so it is centralized instead of in the classes themselves
	def getUnicodeNegationOperator(self):
		return u"\u00AC"

	def getUnicodeConjunctionOperator(self):
		return u" \u2227 "

	def getUnicodeDisjunctionOperator(self):
		return u" \u2228 "

	def getUnicodeConditionalOperator(self):
		return u"\u2192 "

	def getUnicodeBiConditionalOperator(self):
		return u"\u2194 "

	def getUnicodeUniversalOperator(self):
		return u"\u2200"

	def getUnicodeExistentialOperator(self):
		return u"\u2203"

	def getSimpleNegationOperator(self):
		return "~"

	def getSimpleConjunctionOperator(self):
		return "&"

	def getSimpleDisjunctionOperator(self):
		return "|"

	def getSimpleConditionalOperator(self):
		return "->"

	def getSimpleBiConditionalOperator(self):
		return "<->"

	def getSimpleUniversalOperator(self):
		return "@"

	def getSimpleExistentialOperator(self):
		return "#"

	#Also for the hw question
	#Returns True if the Double Negation Equivalence is True
	def checkNegation(self):
		skip=True
		test=Atom()
		testnegation=Negation(Negation(test))
		while True:
			if test.evaluate()!=testnegation.evaluate():
				skip=False
				break
			t=test.nextVal()
			if t:
				break
		return skip

	#Returns the default value, used in the truth tree
	def getDefaultValue(self):
		return self.vals[0]

	#Returns the next value, used in the truth tree, alsoe the first part of the tuple means if it looped through all the values
	def getNextValue(self,v):
		ind=self.vals.index(v)
		if ind==len(self.vals)-1:
			return (True,self.vals[0])
		else:
			return (False,self.vals[ind+1])

	#for the hw as well
	#True if this is the last increment
	def incrementToNextValid(self):
		while True:
			if not self.intial:
				r=self.incrementDefinedVals()
				if r:
					return True
			else:
				self.intial=False
			if self.checkNegation():
				return False

#Defined for our system of logic
#overwrites the functions which were useful in the hw question but pointless when dealing with Trues and Falses
class TrueFalseConstants(Constants):
	def __init__(self):
		self.vals=['T','F']
		self.rs=['F','T','T','F','F','F']

	def incrementToNextValid(self):
		return True

	def checkNegation(self):
		return True

	def incrementDefinedVals(self):
		return True

#Each class represents a type of expression
#There is no parent class, because I found no need for that
#The inner notation of the classes are not standard, notably Conjunction uses expr1 and expr2 while Disjunction, Conditional and Biconditional use ex1 and ex2
#Try and avoid using Conjunction and Disjunction and instead used the Generalized versions
#The Parent structure is not used as of now, but is correctly set up.
#Can use getOperator() function for any expression to figure out what type of expression something is
#equals() is just simple equality, no equivalence rules are used
#  Expr1  |  Expr2  | Expr1.equals(Expr2)
# ----------------------------------------
#   A&B   |   B&A   |      True
#   A|B   |   B|A   |      True
#  A<->B  |  B<->A  |      True
#   A->B  |   B->A  |      False
#   A->B  |  ~A|B   |      False
#   ~~A   |    A    |      False

class Expression:
	def __init__(self):
		pass

	def isGeneralized(self):
		return False

	def swapConstants(self,b,u):
		es=self.toList()
		for e in es:
			e.swapConstants(b,u)

	def getUnboundConstants(self):
		es=self.toList()
		uc=[]
		for e in es:
			uc+=e.getUnboundConstants()
		return list(set(uc))

#I commented Negation Generalized Conjunction and Atom, becuase the others are basically all the same
class Negation(Expression):
	def __init__(self,ex):
		Expression.__init__(self)
		self.expr=ex
		self.parent=None
		self.expr.parent=self

	#Evaluation for the truth tree
	def evaluate(self):
		exval=self.expr.evaluate()
		return con.getNegationVal(exval)

	#Gets a string representation of expression.  Correctly does parenthesis wrapping
	#Setting simp to True uses the simple operator, this is needed for outputing to a file
	def toString(self,simp=False):
		op,cp=getParens(self.expr.getOperator(simp),self.getOperator(simp))
		return self.getOperator(simp)+op+self.expr.toString(simp=simp)+cp

	#Returns the operator
	#used to check what type of expression an object is and for outputing
	#setting simp to true returns the simple operator
	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleNegationOperator()
		return con.getUnicodeNegationOperator()

	#Checks equality
	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return self.expr.equals(ex.expr)
		return False

	def toList(self):
		return [self.expr]

class Conjunction(Expression):
	def __init__(self,ex1,ex2):
		Expression.__init__(self)
		self.expr1=ex1
		self.expr2=ex2
		self.parent=None
		self.expr1.parent=self
		self.expr2.parent=self

	def evaluate(self):
		exval1=self.expr1.evaluate()
		exval2=self.expr2.evaluate()
		return con.getConjunctionVal(exval1,exval2)

	def toString(self,simp=False):
		op1,cp1=getParens(self.expr1.getOperator(simp),self.getOperator(simp))
		op2,cp2=getParens(self.expr2.getOperator(simp),self.getOperator(simp))
		return op1+self.expr1.toString(simp=simp)+cp1+self.getOperator(simp)+op2+self.expr2.toString(simp=simp)+cp2

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleConjunctionOperator()
		return con.getUnicodeConjunctionOperator()

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return (self.expr1.equals(ex.expr1) and self.expr2.equals(ex.expr2)) or (self.expr1.equals(ex.expr2) and self.expr2.equals(ex.expr1))
		return False

	def toList(self):
		return [self.expr1,self.expr2]

#The Generalized versions store a list of expressions
class GeneralizedConjunction(Expression):
	def __init__(self,exs):
		Expression.__init__(self)
		self.exs=[]
		self.parent=None
		#Makes sure that none of the expressions are Conjunctions themselves
		while True:
			addAll=True
			for e in self.exs:
				if e.getOperator()==self.getOperator():
					self.exs.remove(e)
					if e.isGeneralized():
						self.ex+=e.exs
					else:
						self.exs.append(e.expr1)
						self.exs.append(e.expr2)
					addAll=False
					break
			if addAll:
				break
		for e in exs:
			e.parent=self
			self.exs.append(e)

	def evaluate(self):
		val=con.getDefaultValue()
		for e in self.exs:
			val=con.getConjunctionVal(val,e.evaluate())
		return val

	def toString(self,simp=False):
		s=""
		for e in self.exs:
			op,cp=getParens(e.getOperator(simp),self.getOperator(simp))
			s+=op+e.toString(simp=simp)+cp+self.getOperator(simp)
		return s[:-len(self.getOperator(simp))]

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleConjunctionOperator()
		return con.getUnicodeConjunctionOperator()

	def isGeneralized(self):
		return True

	#Makes sure there is a one to one relationship between the two generalized conjunctions
	#there is probably a better way to do this, i think
	def equals(self,ex):
		if ex.getOperator()==self.getOperator() and ex.isGeneralized():
			if len(self.exs)!=len(ex.exs):
				return False
			inds=[]
			for se in self.exs:
				one=False
				for i,oe in enumerate(ex.exs):
					if se.equals(oe) and not(i in inds):
						one=True
						inds.append(i)
						break
				if not one:
					return False
			return True
		return False

	def toList(self):
		return self.exs

class Disjunction(Expression):
	def __init__(self,ex1,ex2):
		Expression.__init__(self)
		self.expr=Negation(Conjunction(Negation(ex1),Negation(ex2)))
		self.ex1=ex1
		self.ex2=ex2
		self.parent=None
		self.ex1.parent=self
		self.ex2.parent=self

	def evaluate(self):
		return self.expr.evaluate()

	def toString(self,simp=False):
		op1,cp1=getParens(self.ex1.getOperator(simp),self.getOperator(simp))
		op2,cp2=getParens(self.ex2.getOperator(simp),self.getOperator(simp))
		return op1+self.ex1.toString(simp=simp)+cp1+self.getOperator(simp)+op2+self.ex2.toString(simp=simp)+cp2

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleDisjunctionOperator()
		return con.getUnicodeDisjunctionOperator()

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return (self.ex1.equals(ex.ex1) and self.ex2.equals(ex.ex2)) or (self.ex1.equals(ex.ex2) and self.ex2.equals(ex.ex1))
		return False

class GeneralizedDisjunction(Expression):
	def __init__(self,exs):
		Expression.__init__(self)
		self.exs=[]
		self.parent=None
		while True:
			addAll=True
			for e in exs:
				if e.getOperator()==self.getOperator():
					exs.remove(e)
					exs.append(e.ex1)
					exs.append(e.ex2)
					addAll=False
					break
			if addAll:
				break

		for e in exs:
			e.parent=self
			self.exs.append(e)

	def evaluate(self):
		val=con.getNegationVal(con.getDefaultValue())
		for e in self.exs:
			val=con.getDisjunctionVal(val,e.evaluate())
		return val

	def toString(self,simp=False):
		s=""
		for e in self.exs:
			op,cp=getParens(e.getOperator(simp),self.getOperator(simp))
			s+=op+e.toString(simp=simp)+cp+self.getOperator(simp)
		return s[:-len(self.getOperator(simp))]

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleDisjunctionOperator()
		return con.getUnicodeDisjunctionOperator()

	def isGeneralized(self):
		return True

	def equals(self,ex):
		if ex.getOperator()==self.getOperator() and ex.isGeneralized():
			if len(self.exs)!=len(ex.exs):
				return False
			inds=[]
			for se in self.exs:
				one=False
				for i,oe in enumerate(ex.exs):
					if se.equals(oe) and not(i in inds):
						one=True
						inds.append(i)
						break
				if not one:
					return False
			return True
		return False

	def toList(self):
		return self.exs

class Conditional(Expression):
	def __init__(self,ex1,ex2):
		Expression.__init__(self)
		self.expr=Negation(Conjunction(ex1,Negation(ex2)))
		self.ex1=ex1
		self.ex2=ex2
		self.parent=None
		self.ex1.parent=self
		self.ex2.parent=self

	def evaluate(self):
		return self.expr.evaluate()

	def toString(self,simp=False):
		op1,cp1=getParens(self.ex1.getOperator(simp))
		op2,cp2=getParens(self.ex2.getOperator(simp))
		return op1+self.ex1.toString(simp=simp)+cp1+self.getOperator(simp)+op2+self.ex2.toString(simp=simp)+cp2

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleConditionalOperator()
		return con.getUnicodeConditionalOperator()

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return (self.ex1.equals(ex.ex1) and self.ex2.equals(ex.ex2))
		return False

	def toList(self):
		return [self.ex1,self.ex2]

class Biconditional(Expression):
	def __init__(self,ex1,ex2):
		Expression.__init__(self)
		self.expr=Conjunction(Conditional(ex1,ex2),Conditional(ex2,ex1))
		self.ex1=ex1
		self.ex2=ex2
		self.parent=None
		self.ex1.parent=self
		self.ex2.parent=self

	def evaluate(self):
		return self.expr.evaluate()

	def toString(self,simp=False):
		op1,cp1=getParens(self.ex1.getOperator(simp))
		op2,cp2=getParens(self.ex2.getOperator(simp))
		return op1+self.ex1.toString(simp=simp)+cp1+self.getOperator(simp)+op2+self.ex2.toString(simp=simp)+cp2

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleBiConditionalOperator()
		return con.getUnicodeBiConditionalOperator()

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return (self.ex1.equals(ex.ex1) and self.ex2.equals(ex.ex2)) or (self.ex1.equals(ex.ex2) and self.ex2.equals(ex.ex1))
		return False

	def toList(self):
		return [self.ex1,self.ex2]

class Universal(Expression):
	def __init__(self,ex,bcon):
		Expression.__init__(self)
		if not bcon.isBound():
			raise Exception('Unbound constant supplied to Universal')
		ex.parexpr=self
		self.expr=ex
		self.con=bcon
		self.con.parexpr=self

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleUniversalOperator()
		return con.getUnicodeUniversalOperator()

	def toString(self,simp=False):
		op,cp=getParens(self.expr.getOperator(simp),self.getOperator(simp))
		return self.getOperator(simp)+self.con.toString()+op+self.expr.toString(simp=simp)+cp

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return self.expr.equals(ex.expr) and self.con.equals(ex.con)
		return False

	def replaceBound(self,ubon):
		if ubon.isBound():
			return None
		copy=cop.copyExpression(self.expr)
		copy.swapConstants(self.con,ubon)
		return copy

	def toList(self):
		return [self.expr]

class Existential(Expression):
	def __init__(self,ex,bcon):
		Expression.__init__(self)
		if not bcon.isBound():
			raise Exception('Unbound constant supplied to Universal')
		ex.parexpr=self
		self.expr=ex
		self.con=bcon
		self.con.parexpr=self

	def getOperator(self,simp=False):
		if simp:
			return con.getSimpleExistentialOperator()
		return con.getUnicodeExistentialOperator()

	def replaceBound(self,ubon):
		if ubon.isBound():
			return None
		copy=cop.copyExpression(self.expr)
		copy.swapConstants(self.con,ubon)
		return copy

	def toString(self,simp=False):
		op,cp=getParens(self.expr.getOperator(simp),self.getOperator(simp))
		return self.getOperator(simp)+self.con.toString()+op+self.expr.toString(simp=simp)+cp

	def equals(self,ex):
		if ex.getOperator()==self.getOperator():
			return self.expr.equals(ex.expr) and self.con.equals(ex.con)
		return False

	def toList(self):
		return [self.expr]

#Atoms is special because its equality is based on pointers, thus two Atoms are the same only if they are the same pointer
#The pointer is form the truthtable
class Atom(Expression):
	def __init__(self,name):
		Expression.__init__(self)
		self.val=con.getDefaultValue()
		self.name=name

	def evaluate(self):
		return self.val

	def getOperator(self,simp=False):
		return ""

	#Used by truthtable
	#true if looped back
	def nextVal(self):
		(rv,nv)=con.getNextValue(self.val)
		self.val=nv
		return rv

	#Truthtable
	def reset(self):
		self.val=con.getDefaultValue()

	def toString(self,simp=False):
		return self.name

	#Needs to be the same pointer
	def equals(self,ex):
		if ex.getOperator()==self.getOperator() and self==ex:
			return True
		try:
			if ex.numcons==0 and ex.atom.equals(self):
				return True
		except Exception, e:
			pass
		return False

	def toList(self):
		return []

class FOAtom(Expression):
	def __init__(self,atom,vs):
		Expression.__init__(self)
		self.atom=atom
		self.numcons=len(vs)
		self.val=con.getDefaultValue()
		self.vs=vs
		for v in self.vs:
			v.childatoms.append(self)

	def evaluate(self):
		if self.numcons>0:
			raise Exception('First Order Atoms do not have truth values')
		return self.val

	def nextVal(self):
		if self.numcons>0:
			raise Exception('First Order Atoms do not have truth values')
		(rv,nv)=con.getNextValue(self.val)
		self.val=nv
		return rv

	def reset(self):
		if self.numcons>0:
			raise Exception('First Order Atoms do not have truth values')
		self.val=con.getDefaultValue()

	def getOperator(self,simp=False):
		return ""

	def toString(self,simp=False):
		s=self.atom.toString()
		if self.numcons==0:
			return s
		s+='('
		for v in self.vs:
			s+=v.toString()+","
		return s[:-1]+")"

	def swapConstants(self,b,u):
		self.replace(b,u)

	def replace(self,cold,cnew):
		for i,c in enumerate(self.vs):
			if c==cold:
				cnew.childatoms.append(self)
				self.vs[i]=cnew

	def equals(self,ex):
		#incase not a FOAtom
		try:
			if self.atom.equals(ex.atom):
				if self.numcons!=ex.numcons:
					return False
				#Order matters
				for i,v in enumerate(self.vs):
					if not v.equals(ex.vs[i]):
						return False
				return True
			return False
		except Exception, e:
			if self.numcons==0 and self.atom.equals(ex):
				return True
			return False

	def toList(self):
		return []

	def getUnboundConstants(self):
		return [v for v in self.vs if not v.isBound()]

class BoundConstant:
	def __init__(self,name):
		self.name=name
		self.parexpr=None
		self.childatoms=[]

	def toString(self,simp=False):
		return self.name

	def equals(self,con):
		if con.isBound():
			return self.depth()==con.depth()
		return False

	def depth(self):
		expr=self.parexpr
		uni= expr.getOperator()==con.getUnicodeUniversalOperator()
		s=0
		while True:
			expr=expr.expr
			if uni and expr.getOperator()==con.getUnicodeUniversalOperator():
				continue
			if not uni and expr.getOperator()==con.getUnicodeUniversalOperator():
				uni=not uni
				s+=1
				continue
			if not uni and expr.getOperator()==con.getUnicodeExistentialOperator():
				continue
			if uni and expr.getOperator()==con.getUnicodeExistentialOperator():
				uni=not uni
				s+=1
				continue
			break
		return s

	def isBound(self):
		return True

class UnBoundConstant:
	def __init__(self,name):
		self.name=name
		self.parexpr=None
		self.childatoms=[]

	def toString(self,simp=False):
		return self.name

	def equals(self,con):
		return self==con

	def isBound(self):
		return False

#Instance of the Constants that is referenced in other scripts
class LogicCopier:
	def __init__(self,cons=None):
		if cons==None:
			self.cons={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"FOAtom":FOAtom,"Universal":Universal,"Existential":Existential}
		else:
			self.cons=cons
		self.ops=con.getUnicodeOperators()
	def copyExpression(self,expr):
		if expr.getOperator()==self.ops["Negation"]:
			return self.cons["Negation"](self.copyExpression(expr.expr))
		if expr.getOperator()==self.ops["Conjunction"]:
			ne=[]
			for e in expr.exs:
				ne.append(self.copyExpression(e))
			return self.cons["Conjunction"](ne)
		if expr.getOperator()==self.ops["Disjunction"]:
			ne=[]
			for e in expr.exs:
				ne.append(self.copyExpression(e))
			return self.cons["Disjunction"](ne)
		if expr.getOperator()==self.ops["Conditional"]:
			return self.cons["Conditional"](self.copyExpression(expr.ex1),self.copyExpression(expr.ex2))
		if expr.getOperator()==self.ops["BiConditional"]:
			return self.cons["Biconditional"](self.copyExpression(expr.ex1),self.copyExpression(expr.ex2))
		if expr.getOperator()=='':
			return self.cons["FOAtom"](expr.atom,list(expr.vs))
		if expr.getOperator()==self.ops["Universal"]:
			return self.cons["Universal"](self.copyExpression(expr.expr),expr.con)
		if expr.getOperator()==self.ops["Existential"]:
			return self.cons["Existential"](self.copyExpression(expr.expr),expr.con)


#Figures out the parens issue
def getParens(childop,selfop=None):
	if childop==con.getSimpleNegationOperator() or childop==con.getUnicodeNegationOperator() or childop=='' or childop==selfop or childop==con.getSimpleExistentialOperator() or childop==con.getUnicodeExistentialOperator() or childop==con.getSimpleUniversalOperator() or childop==con.getUnicodeUniversalOperator():
		return ('','')
	return ('(',')')


con=TrueFalseConstants()
cop=LogicCopier()