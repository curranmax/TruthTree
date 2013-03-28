from truthtree import *
from Tkinter import *
from tkFont import Font

class TruthTreeFrame(Frame):
	def __init__(self,guiparent,reader):
		Frame.__init__(self, guiparent,background="#555")
		self.total=TotalTruthTreeMake(self,reader)
		self.width=500
		self.height=500
		self.guiparent.geometry(str(self.width)+"x"+str(self.height)+"+300+300")

class TotalTruthTreeMake(Canvas):
	def __init__(self,guiparent,reader):
		self.width=500
		self.height=500
		Canvas.__init__(self, guiparent,background="#333",width=self.width,height=self.height)
		self.top=TruthTreeMake(total=self,guiparent=self)
		self.intialize(reader)

		self.top.addChildren()
		P=FOAtomTT(Atom('P'),[])
		self.top.rchild.expressions.append(P)
		self.top.lchild.expressions.append(P)

		self.guiparent=guiparent
		
		self.font=Font(family="Helvetica",size="16")
		self.hpadding=40
		self.wpadding=40
		self.initUI()
				
	def initUI(self):
		self.guiparent.title("Truth Tree")
		self.pack(fill=BOTH, expand=1)
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
		x1=px+t.width/2-10
		y1=py+t.height
		x2=rpx+t.rchild.width/2
		y2=rpy
		self.create_line(x1,y1,x2,y2,fill="red")
		x1=px+t.width/2-10
		x2=lpx+t.lchild.width/2
		y2=lpy
		self.create_line(x1,y1,x2,y2,fill="red")
		self.drawLines(t.rchild)
		self.drawLines(t.lchild)


class TruthTreeMake(TruthTree,Label):
	def __init__(self,parent=None,ten=False,total=None,guiparent=None):
		TruthTree.__init__(self,parent,ten)
		Label.__init__(self,guiparent,background="white",borderwidth=0)
		self.total=total
		self.guiparent=guiparent
		self.width=0
		self.height=0
		self.position=None
		self.labels=[]
		self.bound=None
		self.maxWidth=None
		
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
		for l in self.labels:
			l.grid_remove()
		self.labels=[]
		self.width=0
		self.height=0
		for i,e in enumerate(self.expressions):
			w=self.guiparent.font.measure(e.toString())
			self.height+=self.guiparent.font.metrics("linespace")
			if w>self.width:
				self.width=w
			l=Label(self,text=e.toString(),background="white",font=self.guiparent.font,borderwidth=0)
			l.grid(row=i)
			self.labels.append(l)

	def computePosition(self):
		xmin,xmax=self.getBounds()
		if self.isLeaf():
			x=xmin
		else:
			x=(xmax-xmin+self.rchild.getMaxWidth()-self.lchild.getMaxWidth())/2-self.width/2
		y=self.getCeiling()+self.guiparent.hpadding
		return (x,y)

	def getMaxWidth(self):
		if self.maxWidth!=None:
			return self.maxWidth
		if self.isLeaf():
			self.maxWidth=self.width
			return self.width
		self.maxWidth=max(self.width,self.rchild.maxWidth()+self.lchild.maxWidth()+self.guiparent.wpadding)
		return self.maxWidth

	def getBounds(self):
		if self.bound!=None:
			return self.bound
		if self.parent==None:
			bound=(0,self.guiparent.width)
			return (0,self.guiparent.width)
		wmin,wmax=self.parent.getBounds()
		if self.parent.rchild==self:
			c=wmin+(wmax-wmin-self.getMaxWidth()-self.parent.lchild.getMaxWidth()-self.guiparent.wpadding)/2
			self.bound=(c,c+self.getMaxWidth())
		if self.parent.lchild==self:
			h=wmax-(wmax-wmin-self.getMaxWidth()-self.parent.lchild.getMaxWidth()-self.guiparent.wpadding)/2
			self.bound=(h-self.getMaxWidth(),h)
		return self.bound

	def getCeiling(self):
		if self.parent==None:
			return 0
		return self.parent.computePosition()[1]+self.parent.height

def main():
	root = Tk()
	reader=OffsetLogicReader('validargs.txt',4,{"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT,"FOAtom":FOAtomTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalTT,"Existential":ExistentialTT})
	tree=TotalTruthTreeMake(root,reader)
	root.mainloop()  


if __name__ == '__main__':
	main()