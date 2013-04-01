from truthtree import *
from Tkinter import *
from tkFont import Font

userpredictions={'Neither':'N','Valid':'V','Invalid':'I'}

#LOADING AND SAVING
class TotalTruthTreeMake(Canvas):
	def __init__(self,guiparent,initfile,initoffset=None,w=500,h=500):
		self.guiparent=guiparent
		self.borderwidth=5
		self.width=w
		self.height=h
		Canvas.__init__(self, guiparent,background="#333",width=self.width,height=self.height)
		self.guiparent.geometry(str(self.width)+"x"+str(self.height)+"+300+300")
		self.userprediction=userpredictions['Neither']
		self.load(initfile,initoffset)
		self.save('out2.txt')
		self.font=Font(family="Helvetica",size="16")
		self.buttonfont=Font(family="Helvetica",size="12")
		self.hpadding=40
		self.wpadding=40
		
		self.initUI()
		
	def initUI(self):
		self.guiparent.title("Truth Tree")
		self.pack(fill=BOTH, expand=1)
		self.renderUI()

	def renderUI(self):
		ts=self.top.toList()
		for t in ts:
			t.updateText()
		for t in ts:
			x,y=t.computePosition()
			t.place(x=x,y=y)
		self.drawLines()

	def intialize(self,argreader=None,actreader=None):
		if argreader!=None:
			es=list(argreader.expressions)
			cons=list(argreader.unboundconstants)
			for e in es[:-1]:
				e.treesrc=self.top
			self.top.premises=list(es[:-1])
			self.top.conclusion=es[-1]
			self.top.expressions=list(es[:-1])
			conclusion=NegationTT(es[-1])
			conclusion.treesrc=self.top
			self.top.expressions.append(conclusion)
			self.unboundconstants=list(cons)
		elif actreader!=None:
			self.userprediction=actreader.result
			ps=actreader.premises
			for p in ps:
				p.treesrc=self.top
			c=actreader.conclusion
			cons=actreader.unboundconstantsinarguement
			fas=actreader.factions
			self.top.premises=list(ps)
			self.top.conclusion=c
			nc=NegationTT(c)
			nc.treesrc=self.top
			self.top.expressions=ps+[nc]
			self.unboundconstants=list(cons)
			for fa in fas:
				self.applyForwardAction(fa)
		else:
			raise Exception('None input specified')

	def applyForwardAction(self,fa):
		if isinstance(fa,ForwardOpenLeafAction):
			return self.applyForwardOpenLeafAction(fa)
		if isinstance(fa,ForwardClosedLeafAction):
			return self.applyForwardClosedLeafAction(fa)
		if isinstance(fa,ForwardAddSplitAction):
			return self.applyForwardAddSplitAction(fa)

	def applyForwardOpenLeafAction(self,fa):
		ts=self.top.getTreeSection(fa.tree)
		if ts==None:
			raise Exception('Invalid Tree Section')
		ts.setOpen(fa.opnum)

	def applyForwardClosedLeafAction(self,fa):
		ts=self.top.getTreeSection(fa.tree)
		if ts==None:
			raise Exception('Invalid Tree Section')
		ts.setClosed(fa.opnum)

	def applyForwardAddSplitAction(self,fa):
		srctree=self.top.getTreeSection(fa.srctree)
		if srctree==None:
			raise Exception("Tree Section doesn't exist")
		srce=fa.srce
		opnum=fa.opnum
		addop=self.parseAddOp(fa.addop,srce)
		srce.userSplit(op=opnum)
		dests=[]
		for e,d in fa.dests:
			dt=self.top.getTreeSection(d)
			if dt==None:
				pdt=self.top.getTreeSection(d[:-1])
				if pdt==None:
					raise Exception("Tree Section doesn't exist")
				pdt.addChildren()
				dt=self.top.getTreeSection(d)
			dt.expressions.append(e)
			e.treesrc=dt
			dests.append((e,dt))
		self.top.addActionToTop(AddSplitAction(srctree,srce,dests,addop,opnum))

	#Simplified version from checker
	def parseAddOp(self,op,e):
		#Returns version stored in the overall unboundconstants list, if somehow it is not in there, creates a new one
		if e.getOperator()==con.getUnicodeExistentialOperator() or e.getOperator()==con.getUnicodeUniversalOperator():
			newuc=None
			for uc in self.unboundconstants:
				if uc.name==op:
					newuc=uc
					break
			if newuc==None:
				newuc=UnBoundConstant(op)
				self.unboundconstants.append(newuc)
				return newuc
			return newuc
		#parses the list of ints if there is one
		elif e.getOperator()==con.getUnicodeDisjunctionOperator() or (e.getOperator()==con.getUnicodeNegationOperator() and e.expr.getOperator()==con.getUnicodeConjunctionOperator()):
			if e.getOperator()==con.getUnicodeDisjunctionOperator():
				es=e.toList()
			if e.getOperator()==con.getUnicodeNegationOperator() and e.expr.getOperator()==con.getUnicodeConjunctionOperator():
				es=e.expr.toList()
			if len(es)==2:
				return None
			ns=[int(v) for v in op.split(',')]
			return ns
		else:
			return None

	def drawLines(self,t=None):
		if t==None:
			t=self.top
		if t.isLeaf():
			return
		px,py=t.computePosition()
		rpx,rpy=t.rchild.computePosition()
		lpx,lpy=t.lchild.computePosition()
		x1=px+t.width/2
		y1=py+t.height
		x2=rpx+t.rchild.width/2
		y2=rpy
		if t.rchildline==None:
			t.rchildline=self.create_line(x1,y1,x2,y2,fill="red")
		else:
			self.coords(t.rchildline,x1,y1,x2,y2)
		x1=px+t.width/2
		x2=lpx+t.lchild.width/2
		y2=lpy
		if t.lchildline==None:
			t.lchildline=self.create_line(x1,y1,x2,y2,fill="red")
		else:
			self.coords(t.lchildline,x1,y1,x2,y2)
		self.drawLines(t.rchild)
		self.drawLines(t.lchild)

	def save(self,fname):
		writeTreeToFile(self.top,fname,append=False,result=self.userprediction)

	#Tries to load the file, first by trying if its an action file, then if it is an arguement file
	def load(self,fname,offset=None):
		#check if things have been saved before erasing existing tree
		self.top=TruthTreeMake(total=self,guiparent=self)
		if offset==None:
			try:
				self.loadActionFile(fname)
				return
			except Exception, e:
				pass
		try:
			self.loadArguementFile(fname,offset)
			return
		except Exception, e:
			raise e
		#Make this a pop up if you can
		print "Invalid File"

	def loadActionFile(self,fname):
		actionreader=TruthTreeReader(fname)
		self.intialize(actreader=actionreader)

	def loadArguementFile(self,fname,offset=None):
		c={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT,"FOAtom":FOAtomTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalTT,"Existential":ExistentialTT}
		if offset!=None:
			reader=OffsetLogicReader(fname,offset,c)
		else:
			reader=LogicReader(fname,c)
		self.intialize(argreader=reader)


class TruthTreeMake(TruthTree,Label):
	def __init__(self,parent=None,ten=False,total=None,guiparent=None):
		TruthTree.__init__(self,parent,ten)
		Label.__init__(self,guiparent,background="white",borderwidth=guiparent.borderwidth)
		self.total=total
		self.guiparent=guiparent
		self.width=0
		self.height=0
		self.splitbuttontext="Split"
		self.position=None
		self.labels=[]
		self.bound=None
		self.maxWidth=None
		self.rchildline=None
		self.lchildline=None
		
	def getTotal(self):
		t=self
		while t.parent!=None:
			t=t.parent
		return t.total

	#Adds empty children to the tree section
	def addChildren(self,ten=False):
		self.rchild=TruthTreeMake(self,ten,guiparent=self.guiparent)
		self.lchild=TruthTreeMake(self,ten,guiparent=self.guiparent)

	def toList(self):
		if self.isLeaf():
			return [self]
		return [self]+self.rchild.toList()+self.lchild.toList()

	def updateText(self):
		self.resetVariables()
		for i,e in enumerate(self.expressions):
			w=self.guiparent.font.measure(e.toString())
			if w>self.width:
				self.width=w
			l=Label(self,text=e.toString(),background="white",font=self.guiparent.font)
			l.grid(row=i,padx=0,pady=0)
			self.labels.append(l)
		self.width+=2*self.guiparent.borderwidth
		self.addButtons()

	def addButtons(self):
		h=0
		for i,e in enumerate(self.expressions):
			b=Button(self,text=self.splitbuttontext,font=self.guiparent.buttonfont,width=2,height=1)
			b.grid(row=i,column=1,padx=0,pady=0,sticky=E)
		self.width+=self.guiparent.buttonfont.measure(self.splitbuttontext)+4
		self.height=10+(len(self.expressions))*35

	def computePosition(self):
		xmin,xmax=self.getBounds()
		if self.position!=None:
			return self.position
		if self.isLeaf():
			x=(xmax+xmin-self.width)/2
		else:
			rw=self.rchild.getMaxWidth()
			lw=self.lchild.getMaxWidth()
			if(rw+lw+self.guiparent.wpadding>self.width):
				x=(xmax+xmin+rw-lw-self.width)/2
			else:
				x=(xmax+xmin-self.width)/2
		y=self.getCeiling()+self.guiparent.hpadding
		self.position=(x,y)
		return (x,y)

	def getMaxWidth(self):
		if self.maxWidth!=None:
			return self.maxWidth
		if self.isLeaf():
			self.maxWidth=self.width
			return self.width
		self.maxWidth=max(self.width,self.rchild.getMaxWidth()+self.lchild.getMaxWidth()+self.guiparent.wpadding)
		return self.maxWidth

	def getBounds(self):
		if self.bound!=None:
			return self.bound
		if self.parent==None:
			bound=(0,self.guiparent.width)
			return (0,self.guiparent.width)
		wmin,wmax=self.parent.getBounds()
		if self.parent.rchild==self:
			c=(wmax+wmin-self.getMaxWidth()-self.guiparent.wpadding-self.parent.lchild.getMaxWidth())/2
			self.bound=(c,c+self.getMaxWidth())
		if self.parent.lchild==self:
			h=(wmax+wmin+self.getMaxWidth()+self.parent.rchild.getMaxWidth()+self.guiparent.wpadding)/2
			self.bound=(h-self.getMaxWidth(),h)
		return self.bound

	def getCeiling(self):
		if self.parent==None:
			return 0
		return self.parent.computePosition()[1]+self.parent.height

	def resetVariables(self):
		self.width=0
		self.height=0
		self.position=None
		self.bound=None
		self.maxWidth=None
		for l in self.labels:
			l.grid_remove()
		self.labels=[]

def main():
	root = Tk()
	tree=TotalTruthTreeMake(root,'validargs.txt',initoffset=4,w=root.winfo_screenwidth()-100,h=root.winfo_screenheight()-100)
	root.mainloop()  


if __name__ == '__main__':
	main()