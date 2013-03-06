from logicdefintions import *


#Lists of the operators from the instance of Constants in logicdefinitions

#Unary operators precede an expression
#Right now is just Negation, but will include Existenstial and Univerisal
uoperators=con.getSimpleUnaryOperators()
#Binary have an expression to the right and left of the expression
boperators=con.getSimpleBinaryOperators()

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
		if constructors==None:
			#Default constructor
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom}
		else:
			self.constructors=constructors
		#Parses each line into an expression by calling findExpression on each line
		f=open(fname)
		for line in f:
			expr=line
			if expr=="\n":
				break
			self.expressions.append(self.findExpression(expr))
		f.close()

	#Parses a string into an expression, ensuring that atoms are shared
	def findExpression(self,expression):
		#gets rid of any whitespace
		nspace=expression.split()
		expression=""
		for ns in nspace:
			expression+=ns

		if expression=='':
			raise IOError('Invalid Input File')
		expr=None
		#Determine if Atom
		atom=self.isAtom(expression)
		if atom!=None:
			return atom

		#Splits expression up to subexpression, and tells which operator was removed
		(o,split)=self.breakExpression(expression)

		#Recusively finds the subexpressions and based on o puts those into the correct expression

		#Just removed Parenthesises
		if o=='(':
			expr=self.findExpression(split[0])


		#Negation
		if o=='~':
			expr=self.constructors["Negation"](self.findExpression(split[0]))

		if o=='&':
			exs=[]
			for s in split:
				exs.append(self.findExpression(s))
			expr=self.constructors["Conjunction"](exs)
		if o=='|':
			exs=[]
			for s in split:
				exs.append(self.findExpression(s))
			expr=self.constructors["Disjunction"](exs)
		if o=='->':
			expr=self.constructors["Conditional"](self.findExpression(split[0]),self.findExpression(split[1]))
		if o=='<->':
			expr=self.constructors["Biconditional"](self.findExpression(split[0]),self.findExpression(split[1]))
		return expr

	#Determines if it is an atom
	#Currently it just needs to be only capitol letters
	def isAtom(self,expression):
		for c in expression:
			if not(c>="A" and c<="Z"):
				return None

		a=self.getAtom(expression)
		return a

	#Finds the atom with the same name
	#If none exists then a new atom is made
	def getAtom(self,name):
		for a in self.atoms:
			if a.name==name:
				return a
		a=self.constructors["Atom"](name)
		self.atoms.append(a)
		return a

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

#Uses the find expression of LogicReader to parse single strings
#Not really necessary, but it just separates the two operations from each other
#Really inheritance should be flipped, b/c the filereader uses the stringparser, but I wrote the filereader first
class LogicString(LogicReader):
	def __init__(self,constructors=None,atoms=[]):
		self.atoms=atoms
		if constructors==None:
			self.constructors={"Conjunction":GeneralizedConjunction,"Negation":Negation,"Disjunction":GeneralizedDisjunction,"Conditional":Conditional,"Biconditional":Biconditional,"Atom":Atom}
		else:
			self.constructors=constructors

	def parseString(self,string):
		return self.findExpression(string)