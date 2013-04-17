from logicdefintions import *


#Lists of the operators from the instance of Constants in logicdefinitions

#Unary operators precede an expression
#Right now is just Negation, but will include Existenstial and Univerisal
uoperators=con.getSimpleUnaryOperators()
#Binary have an expression to the right and left of the expression
boperators=con.getSimpleBinaryOperators()
commentstring="//"

#Reads in an arguement file and parses the strings into objects
#***************************************IMPORTANT***************************************
#Atoms, such as P, Q, or R, are saved, such that there is only one instance of it, and that instance is pointed to by any expression they have them. 
class LogicReader:
	#fname is the path to the arguement file
	#constructors is a dictionary of constructors for types, the conjunction and disjunction must be generalized
	#atoms allow for the sharing of atoms between readers
	def __init__(self,fname,constructors=None,atoms=[]):
		self.atoms=atoms
		self.expressions=[]
		self.unboundconstants=[]
		self.boundencounetered=[]
		if constructors==None:
			#Default constructor
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom,"FOAtom":FOAtom,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":Universal,"Existential":Existential}
		else:
			self.constructors=constructors
		#Parses each line into an expression by calling findExpression on each line
		f=open(fname)
		for line in f:
			expr=line
			if expr=="\n":
				break
			expr=self.removeComments(expr)
			if expr=="":
				continue
			self.expressions.append(self.findExpression(expr))

		f.close()
	#Parses a string into an expression, ensuring that atoms are shared
	def findExpression(self,expression,bound=[]):
		#gets rid of any whitespace
		nspace=expression.split()
		expression=""
		for ns in nspace:
			expression+=ns

		if expression=='':
			raise IOError('Invalid Input File')
		expr=None
		#Determine if Atom
		atom=self.isAtom(expression,bound)
		if atom!=None:
			return atom

		#Splits expression up to subexpression, and tells which operator was removed
		(o,split)=self.breakExpression(expression)

		#Recusively finds the subexpressions and based on o puts those into the correct expression

		#Just removed Parenthesises
		if o=='(':
			expr=self.findExpression(split[0],bound)

		if o=='~':
			expr=self.constructors["Negation"](self.findExpression(split[0],bound))
		if o=='@':
			(uv,restexpr)=self.getVariable(split[0],bound)
			expr=self.constructors["Universal"](self.findExpression(restexpr,bound+[uv]),uv)
		if o=='#':
			(uv,restexpr)=self.getVariable(split[0],bound)
			expr=self.constructors["Existential"](self.findExpression(restexpr,bound+[uv]),uv)

		if o=='&':
			exs=[]
			for s in split:
				exs.append(self.findExpression(s,bound))
			expr=self.constructors["Conjunction"](exs)
		if o=='|':
			exs=[]
			for s in split:
				exs.append(self.findExpression(s,bound))
			expr=self.constructors["Disjunction"](exs)
		if o=='->':
			expr=self.constructors["Conditional"](self.findExpression(split[0],bound),self.findExpression(split[1],bound))
		if o=='<->':
			expr=self.constructors["Biconditional"](self.findExpression(split[0],bound),self.findExpression(split[1],bound))
		return expr

	#Determines if it is an atom
	#Currently it just needs to be only capitol letters
	def isAtom(self,expression,bound):
		fo=False
		for i,c in enumerate(expression):
			if c=='(':
				fo=True
				break
			if not(c>="A" and c<="Z"):
				return None
		if not fo:
			a=self.getAtom(expression)
			return self.constructors["FOAtom"](a,[])
		a=self.getAtom(expression[:i])
		stringcon=expression[i+1:-1].split(',')
		cons=[]
		for poscon in stringcon:
			pc=self.getConstant(poscon,bound)
			if pc==None:
				return None
			cons.append(pc)
		return self.constructors["FOAtom"](a,cons)

	#Finds the atom with the same name
	#If none exists then a new atom is made
	def getAtom(self,name):
		for a in self.atoms:
			if a.name==name:
				return a
		a=self.constructors["Atom"](name)
		self.atoms.append(a)
		return a

	def getConstant(self,scon,bound,make=True):
		for c in scon:
			if not(c>="a" and c<="z"):
				return None
		for c in bound:
			if c.name==scon:
				return c
		for c in self.unboundconstants:
			if c.name==scon:
				return c
		if make:
			for b in self.boundencounetered:
				if b==scon:
					raise IOError("Variable encountered already in different scope")
			uc=self.constructors["UnBoundConstant"](scon)
			self.unboundconstants.append(uc)
			return uc
		else:
			return None

	def getVariable(self,e,bound):
		for i,c in enumerate(e):
			if not(c>="a" and c<="z"):
				break
		if self.getConstant(e[:i],bound,make=False)!=None:
			raise IOError("Variable Already Bound")
		self.boundencounetered.append(e[:i])
		return (self.constructors["BoundConstant"](e[:i]),e[i:])
	
	#splits the expression on the outermnost operator and returns the subexpressions and operator
	#returns a tuple
	#	The first value is a string of the operator
	#	The second is a list of strings of subexpressions
	def breakExpression(self,expression):
		#Indicates the depth of parenthesis, only interested in operators those not in parenthesis,so when paren=0
		paren=0
		#Intially checks if could be surronded by parenthesises, paren also has to be greater than 0 at every step of the loop
		#POSSIBLE ERROR: (A)(B) might return ('(',['A)(B']) 
		surrondingparen=expression[0]=='(' and expression[-1]==')'
		#What will be returned
		ret=None
		#index of the last operator encountered
		ind=-1
		#first operator found with paren==0
		op=None
		#Parses expression
		for i,c in enumerate(expression):
			if c=='(':
				paren+=1
				continue
			if c==')':
				paren-=1
				continue
			if paren==0:
				surrondingparen=False
				#checks if equal to any operators
				for o in boperators:
					if o==expression[i:i+len(o)]:
						#Since <-> has a -> this case is ignored
						if op=='<->' and o=='->' and i-1==ind:
							continue
						#When you have more than one operator at paren==0 and the operator would create an ambigous statement
						if op!=None and (op!=o or (op!='&' and op!='|')):
							raise IOError('Ambigous Statement in Input File')
						#First operator
						if op==None:
							ret=[expression[:i],expression[i+len(o):]]
							ind=i
							op=o
						#Found more than one operator that match and can be generalized
						else:
							ret=ret[:-1]+[expression[ind+len(op):i],expression[i+len(o):]]
							ind=i

		#Found an operator
		if ret!=None:
			return (op,ret)

		#Removes the surroding parenthesises
		if surrondingparen:
			return ('(',[expression[1:-1]])

		#Checks for unary operators
		for o in uoperators:
			if o==expression[:len(o)]:
				return (o,[expression[len(o):]])
		#Nothing found thus error
		raise IOError('Invalid Input File')

	def removeComments(self,expression):
		com=expression.find(commentstring) 
		if com==-1:
			return expression
		return expression[:com]
#Uses the find expression of LogicReader to parse single strings
#Not really necessary, but it just separates the two operations from each other
#Really inheritance should be flipped, b/c the filereader uses the stringparser, but I wrote the filereader first
class LogicString(LogicReader):
	def __init__(self,constructors=None,atoms=[],unboundconstants=[]):
		self.atoms=atoms
		self.unboundconstants=unboundconstants
		self.boundencounetered=[]
		if constructors==None:
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom}
		else:
			self.constructors=constructors

	def parseString(self,string):
		return self.findExpression(string)

class MultiLogicReader(LogicReader):
	def __init__(self,fname,constructors=None,atoms=[]):
		self.atoms=atoms
		self.expressions=[]
		self.unboundconstants=[]
		self.allunboundconstants=[]
		self.boundencounetered=[]
		if constructors==None:
			#Default constructor
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom,"FOAtom":FOAtom,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":Universal,"Existential":Existential}
		else:
			self.constructors=constructors
		#Parses each line into an expression by calling findExpression on each line
		f=open(fname)
		t=[]
		for line in f:
			expr=line
			if expr=="\n":
				self.expressions.append(t)
				self.allunboundconstants.append(list(self.unboundconstants))
				self.unboundconstants=[]
				self.boundencounetered=[]
				self.atoms=atoms
				com=""
				t=[]
				continue
			expr=self.removeComments(expr)
			if expr=='':
				continue
			t.append(self.findExpression(expr,[]))
		f.close()

class OffsetLogicReader(LogicReader):
	def __init__(self,fname,offset,constructors=None,atoms=[],unboundconstants=[]):
		self.atoms=atoms
		self.expressions=[]
		self.unboundconstants=unboundconstants
		self.boundencounetered=[]
		if constructors==None:
			#Default constructor
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom,"FOAtom":FOAtom,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":Universal,"Existential":Existential}
		else:
			self.constructors=constructors
		f=open(fname)
		com=""
		num=0
		for line in f:
			expr=line
			if expr=="\n":
				if num==offset-1:
					break
				num+=1
				continue
			if num==offset-1:
				expr=self.removeComments(expr)
				if expr=='':
					continue
				self.expressions.append(self.findExpression(expr,[]))
		f.close()