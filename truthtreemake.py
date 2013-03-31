from truthtree import *
from Tkinter import *
from tkFont import Font


#LOADING AND SAVING
class TotalTruthTreeMake(Canvas):
	def __init__(self,guiparent,reader,w=500,h=500):
		self.guiparent=guiparent
		self.borderwidth=5
		self.width=w
		self.height=h
		Canvas.__init__(self, guiparent,background="#333",width=self.width,height=self.height)
		self.guiparent.geometry(str(self.width)+"x"+str(self.height)+"+300+300")
		self.top=TruthTreeMake(total=self,guiparent=self)
		self.intialize(reader)

		self.top.addChildren()
		P=FOAtomTT(Atom('P'),[])
		self.top.rchild.expressions.append(P)
		self.top.lchild.expressions.append(P)
		self.top.rchild.addChildren()
		self.top.lchild.addChildren()
		self.top.rchild.rchild.expressions.append(P)
		self.top.rchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(P)
		self.top.rchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.expressions.append(GeneralizedConjunctionTT([P,P,P,P,P,P,P]))
		self.top.rchild.rchild.addChildren()
		self.top.rchild.lchild.addChildren()
		self.top.lchild.rchild.addChildren()
		self.top.lchild.lchild.addChildren()
		self.top.rchild.rchild.rchild.expressions.append(P)
		self.top.rchild.rchild.lchild.expressions.append(P)
		self.top.rchild.lchild.rchild.expressions.append(P)
		self.top.rchild.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.rchild.expressions.append(P)
		self.top.lchild.rchild.lchild.expressions.append(P)
		self.top.lchild.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.lchild.expressions.append(P)
		self.top.lchild.rchild.rchild.expressions.append(P)
		self.top.lchild.rchild.lchild.expressions.append(P)
		self.top.lchild.lchild.rchild.expressions.append(P)
		self.top.lchild.lchild.lchild.expressions.append(P)

		
		
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

	def intialize(self,reader):
		es=list(reader.expressions)
		cons=list(reader.unboundconstants)
		for e in es[:-1]:
			e.treesrc=self.top
		self.top.premises=list(es[:-1])
		self.top.conclusion=es[-1]
		self.top.expressions=list(es[:-1])
		conclusion=NegationTT(es[-1])
		conclusion.treesrc=self.top
		self.top.expressions.append(conclusion)
		self.unboundconstants=list(cons)

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
		pass

	def load(self,fname):
		pass


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
		print self.actionString(),xmin,xmax
		if self.isLeaf():
			x=xmin
		else:
			rw=self.rchild.getMaxWidth()
			lw=self.lchild.getMaxWidth()
			if(rw+lw+self.guiparent.wpadding>self.width):
				x=(xmax+xmin+rw-lw-self.width)/2
			else:
				x=(xmax+xmin-self.width)/2
		y=self.getCeiling()+self.guiparent.hpadding
		self.position=(x,y)
		print ""
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
	reader=OffsetLogicReader('validargs.txt',4,{"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT,"FOAtom":FOAtomTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalTT,"Existential":ExistentialTT})
	tree=TotalTruthTreeMake(root,reader,w=root.winfo_screenwidth()-100,h=root.winfo_screenheight()-100)
	root.mainloop()  


if __name__ == '__main__':
	main()