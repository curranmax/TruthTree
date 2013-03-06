from logicdefintions import *
from iologic import *

#Makes a truthtable
#Wrote this just as a starting point
#You can use this to test anything
#It doesn't let you specify the file from command line though

class TruthTable:
	def __init__(self):
		self.atoms=[]
		self.expressions=[]

	def addAtom(self,a):
		self.atoms.append(a)

	def addExpression(self,ex):
		self.expressions.append(ex)

	def resetAll(self):
		for a in self.atoms:
			a.reset()

	def readFromFile(self,fname):
		lr=LogicReader("logictest.txt")
		for a in lr.atoms:
			self.addAtom(a)
		for e in lr.expressions:
			self.addExpression(e)
	
	def toString(self):
		self.resetAll()
		ls=0
		colsizes=[]
		coloffset=len(self.atoms)
		header=""
		for a in self.atoms:
			astring=a.toString()
			colsizes.append(len(astring)+2)
			ls+=len(astring)+3
			header+=" "+astring+" |"
		header+="|"
		for e in self.expressions:
			estring=e.toString()
			colsizes.append(len(estring)+2)
			ls+=len(estring)+3
			header+=" "+estring+" |"

		header=header[:-1]
		line=""
		extra=False
		for i,c in enumerate(colsizes):
			line+=c*"-"+"|"
			if not extra and i==coloffset-1:
				line+="|"
				extra=True
		line=line[:-1]
		body=header+"\n"+line+"\n"

		while True:
			for i,a in enumerate(self.atoms):
				astring=a.evaluate()
				nrsp=colsizes[i]/2-len(astring)/2
				nlsp=colsizes[i]-len(astring)-nrsp
				body+=" "*nrsp+astring+" "*nlsp+"|"
			body+="|"
			for i,e in enumerate(self.expressions):
				estring=e.evaluate()
				nrsp=colsizes[i+coloffset]/2-len(estring)/2
				nlsp=colsizes[i+coloffset]-len(estring)-nrsp
				body+=" "*nrsp+estring+" "*nlsp+"|"
			body=body[:-1]+"\n"
			end=False
			for i,a in enumerate(self.atoms[::-1]):
				rv=a.nextVal()
				if not rv:
					break
				if i==len(self.atoms)-1:
					end=True
			if end:
				break
		return body


tt=TruthTable()
tt.readFromFile("logictest.txt")
print tt.toString()