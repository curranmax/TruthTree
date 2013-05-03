from truthtree import *
from Tkinter import *
from tkFont import Font
import tkFileDialog
import tkMessageBox

userpredictions={'Neither':'N','Valid':'V','Invalid':'I'}
invertuserpredictions={'N':'Neither','V':'Valid','I':'Invalid'}
constructors={"Conjunction":GeneralizedConjunctionTT,"Negation":NegationTT,"Disjunction":GeneralizedDisjunctionTT,"Conditional":ConditionalTT,"Biconditional":BiconditionalTT,"Atom":AtomTT,"FOAtom":FOAtomTT,"UnBoundConstant":UnBoundConstant,"BoundConstant":BoundConstant,"Universal":UniversalTT,"Existential":ExistentialTT}

#TODO
#Add a new button so arguements can be entered not from a file
#Position is still a little weird

class TreeWindow(Frame):
	def __init__(self,guiparent,w=500,h=500):
		self.guiparent=guiparent
		self.guiparent.geometry(str(w)+"x"+str(h)+"+300+300")
		self.guiparent.title("Truth Tree")
		Frame.__init__(self,guiparent,background="#555",border=0)
		self.pack(fill=BOTH,expand=1)
		self.userprediction='Neither'
		self.filename=None
		self.menu=MenuBar(self,w,40)
		self.menu.pack(fill=X,expand=1,side=TOP,anchor=N)
		self.total=TotalTruthTreeMake(self,w,h-40)
		self.total.pack(side=TOP,fill=BOTH,padx=0,pady=0,expand=1,anchor=N)

	def save(self,filename=None):
		if filename==None:
			filename=self.filename
		self.filename=filename
		self.userprediction=self.menu.choice.get()
		self.total.save(filename)

	def load(self,filename,offset=None):
		self.filename=self.total.load(filename,offset)
	
	def undo(self):
		if len(self.total.top.actions)==0:
			print "no actions to undo"
		else:
			self.total.undoLastAction()

	def redo(self):
		if len(self.total.redoactions)==0:
			print "no actions to redo"
		else:
			self.total.applyForwardAction(self.total.redoactions[-1])
			self.total.redoactions=self.total.redoactions[:-1]
			self.total.enterNormalState()

class MenuBar(Frame):
	def __init__(self,guiparent,w,h):
		self.guiparent=guiparent
		Frame.__init__(self,guiparent,background="#CCC")
		self.buttonfont=Font(family="Helvetica",size="12")
		self.font=Font(family="Helvetica",size="16")
		self.choice=StringVar()
		self.choice.set(self.guiparent.userprediction)
		self.menu=None
		self.buttons=[]
		self.entries=[]
		self.addUsualButtons()

	def reset(self):
		self.removeAllButtons()
		self.addUsualButtons()

	def addUsualButtons(self):
		self.makeButton("Save",self.saveEvent,0)
		self.makeButton("Save as",self.saveAsEvent,1)
		self.makeButton("Load",self.loadEvent,2)
		self.makeButton("Undo",self.undoEvent,3)
		self.makeButton("Redo",self.redoEvent,4)
		self.addSelectValidityMenu(5)

	def removeAllButtons(self):
		for b in self.buttons:
			b.grid_remove()
		self.buttonts=[]
		for e in self.entries:
			e.grid_remove()
		self.entries=[]
		if self.menu!=None:
			self.menu.grid_remove()
		self.menu=None

	def saveEvent(self,event):
		if self.guiparent.filename==None:
			formats=[('Action File','*.act'),('All Files','*')]
			defaultextension='.act'
			fname=tkFileDialog.asksaveasfilename(parent=self,initialdir="./",title='Save File',defaultextension=defaultextension,filetypes=formats)
			self.guiparent.save(fname)
		else:
			self.guiparent.save()
		self.reset()

	def saveAsEvent(self,event):
		formats=[('Action File','*.act'),('All Files','*')]
		defaultextension='.act'
		fname=tkFileDialog.asksaveasfilename(parent=self,initialdir="./",title='Save File as',defaultextension=defaultextension,filetypes=formats)
		self.guiparent.save(fname)
		self.reset()

	def cancelEvent(self,event):
		self.reset()

	def loadEvent(self,event):
		formats=[('Action and Arguement File','*.act *.arg'),('Action File','*.act'),('Arguement File',"*.arg"),("All files","*")]
		fname=tkFileDialog.askopenfilename(parent=self,initialdir="./",title='Load a file',filetypes=formats)
		try:
			ftype=fname[fname.rfind('.'):]
		except Exception, e:
			self.reset()
			return
		offset=None
		if ftype=='.arg':
			offset=self.askOffset(fname)
			if offset==None:
				print "Invalid Offset"
				return
		if fname!="":
			self.guiparent.load(fname,offset)
		self.reset()

	def askOffset(self,fname):
		i=fname.rfind('/')
		if i==-1:
			i=fname.rfind('\\')
		e=OffsetPopup(self)
		self.wait_window(e.top)
		return e.offset

	def undoEvent(self,event):
		self.guiparent.undo()

	def redoEvent(self,event):
		self.guiparent.redo()

	def makeButton(self,text,event,col):
		button=ButtonWrapper(self,text,self.buttonfont,75,30)
		button.grid(row=0,column=col,sticky=W,padx=5)
		button.bind("<Button-1>",event)
		self.buttons.append(button)

	def makeEntry(self,col,text=''):
		entry=EntryWrapper(self,200,34,self.font,text)
		entry.grid(row=0,column=col,sticky=W,padx=10)
		self.entries.append(entry)

	def addSelectValidityMenu(self,col):
		self.choice.set(self.guiparent.userprediction)
		self.menu=OptionMenu(self, self.choice, *(userpredictions.keys()))
		self.menu.grid(row=0,column=col,sticky=W,padx=10)

class TotalTruthTreeMake(Canvas):
	def __init__(self,guiparent,w=500,h=500):
		self.guiparent=guiparent
		self.borderwidth=5
		self.width=w
		self.height=h
		#overall offset from (0,0)
		self.mx=None
		self.my=None
		self.rx=0
		self.ry=0
		self.dx=10
		self.dy=10
		Canvas.__init__(self, guiparent,background="#333",width=self.width,height=self.height)
		self.stringreader=LogicString(constructors=constructors)
		self.top=None
		self.font=Font(family="Helvetica",size="16")
		self.buttonfont=Font(family="Helvetica",size="12")
		self.hpadding=40
		self.wpadding=40
		self.redoactions=[]
		self.ids=[]
		#Functions to allow for moving
		self.bind("<ButtonPress-1>", self.startMove)
		self.bind("<ButtonRelease-1>", self.stopMove)
		self.bind("<B1-Motion>", self.onMotion)
		self.resetAction()
		self.initUI()

	def startMove(self,event):
		self.mx=event.x
		self.my=event.y

	def stopMove(self,event):
		self.mx=None
		self.my=None

	def onMotion(self,event):
		self.dx=event.x-self.mx
		self.dy=event.y-self.my
		self.moveLabels()
		self.rx+=self.dx
		self.ry+=self.dy
		self.startMove(event)
		
	def moveLabels(self):
		if self.top==None:
			return
		for t in self.ids:
			self.move(t,self.dx,self.dy)
		self.moveLines()

	def moveLines(self,t=None):
		if t==None:
			t=self.top
		if t.isLeaf():
			return
		self.move(t.rchildline,self.dx,self.dy)
		self.move(t.lchildline,self.dx,self.dy)
		self.moveLines(t.rchild)
		self.moveLines(t.lchild)

	def resetAction(self):
		self.selectedexprlabel=None
		self.srctree=None
		self.srce=None
		self.dests=[]
		self.addop=None
		self.opnum=0
		self.added=False

	def addAction(self):
		if len(self.dests)==0 or self.added:
			return
		self.opnum=self.srce.userSplit(adop=self.addop)
		a=AddSplitAction(self.srctree,self.srce,self.dests,self.addop,self.opnum)
		self.top.addActionToTop(a)
		gopnum[0]=self.opnum+1
		self.added=True

	def guessAddop(self,expr):
		if not self.srce.needAddop() or self.addop!=None:
			return
		try:			
			if self.srce.getOperator()==con.getUnicodeDisjunctionOperator():
				if expr.getOperator()!=con.getUnicodeDisjunctionOperator():
					for i,e in enumerate(self.srce.exs):
						if expr.equals(e):
							self.addop=[i]
							return
				else:
					matched=[False]*len(expr.exs)
					inds=[]
					for i,e in enumerate(self.srce.exs):
						for j,ine in enumerate(expr.exs):
							if ine.equals(e) and not matched[j]:
								inds.append(i)
					self.addop=inds
					return
			if self.srce.getOperator()==con.getUnicodeDisjunctionOperator() and self.srce.expr.getOperator()==con.getUnicodeConjunctionOperator():
				if expr.getOperator()==con.getUnicodeDisjunctionOperator() and expr.getOperator()!=con.getUnicodeConjunctionOperator():
					for i,e in enumerate(self.srce.expr.exs):
						if expr.expr.equals(e):
							self.addop=[i]
							return
				else:
					matched=[False]*len(expr.expr.exs)
					inds=[]
					for i,e in enumerate(self.srce.expr.exs):
						for j,ine in enumerate(expr.expr.exs):
							if ine.equals(e) and not matched[j]:
								inds.append(i)
					self.addop=inds
					return
			if self.srce.getOperator()==con.getUnicodeUniversalOperator() or self.srce.getOperator()==con.getUnicodeExistentialOperator():
				constant=self.srce.expr.findSubstitutedConstant(expr)
				self.addop=constant
		except Exception, e:
			print e
			return

	def initUI(self):
		self.enterNormalState()
		
	def enterNormalState(self):
		self.ids=[]
		if self.top==None:
			return
		self.top.removeEmptyChildren()
		ts=self.top.toList()
		for t in ts:
			t.normalState()
		for t in ts:
			x,y=t.computePosition()
			self.ids.append(self.create_window((self.rx+x,self.ry+y),window=t,anchor=NW))
		self.drawLines()
		self.moveLabels()

	def enterEditState(self):
		self.ids=[]
		if self.top==None:
			return
		ts=self.top.toList()
		for t in ts:
			t.editState()
		for t in ts:
			x,y=t.computePosition()
			self.ids.append(self.create_window((self.rx+x,self.ry+y),window=t,anchor=NW))
		self.drawLines()
		self.moveLabels()

	def setSelectedExpression(self,exprlabel):
		if exprlabel==None:
			self.addAction()
		if self.selectedexprlabel!=None:
			self.addAction()
			self.selectedexprlabel.noLongerSelected()
			self.resetAction()
			self.enterNormalState()
		self.selectedexprlabel=exprlabel
		if self.selectedexprlabel!=None:
			self.srctree=self.selectedexprlabel.guiparent
			self.srce=self.selectedexprlabel.expr
			self.enterEditState()

	def addDestEPair(self,e,dest):
		self.guessAddop(e)
		self.dests.append((e,dest))

	def intialize(self,argreader=None,actreader=None):
		if argreader!=None:
			self.stringreader=LogicString(constructors=constructors,atoms=argreader.atoms,unboundconstants=argreader.unboundconstants)
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
			self.stringreader=LogicString(constructors=constructors,atoms=actreader.atoms,unboundconstants=actreader.unboundconstants)
			self.guiparent.userprediction=invertuserpredictions[actreader.result]
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

	def abortEditState(self):
		self.selectedexprlabel.noLongerSelected()
		for e,d in self.dests:
			d.expressions.remove(e)
		self.resetAction()
		self.enterNormalState()

	def undoLastAction(self):
		if self.selectedexprlabel!=None:
			self.abortEditState()
			return
		a=self.top.actions[-1]
		self.top.actions=self.top.actions[:-1]
		if isinstance(a,OpenLeafAction):
			fa=self.undoOpenLeafAction(a)
		if isinstance(a,ClosedLeafAction):
			fa=self.undoClosedLeafAction(a)
		if isinstance(a,AddSplitAction):
			fa=self.undoAddSplitAction(a)
		self.redoactions.append(fa)
		self.enterNormalState()

	def undoOpenLeafAction(self,a):
		t=a.tree
		t.open=False
		op=t.opnum
		gopnum[0]=op
		t.opnum=0
		return ForwardOpenLeafAction(t.actionString(),op)

	def undoClosedLeafAction(self,a):
		t=a.tree
		t.closed=False
		op=t.opnum
		gopnum[0]=op
		t.opnum=0
		return ForwardClosedLeafAction(t.actionString(),op)

	def undoAddSplitAction(self,a):
		se=a.srce
		op=a.opnum
		se.undoSplit(a.addop,op)
		fadests=[]
		for e,d in a.dests:
			d.expressions.remove(e)
			fadests.append((e,d.actionString()))
		straddop=""
		if a.addop==None:
			straddop="None"
		elif isinstance(a.addop,list):
			for v in a.addop:
				straddop+=str(v)+","
			straddop=straddop[:-1]
		else:
			straddop=a.addop.name
		return ForwardAddSplitAction(a.srctree.actionString(),se,fadests,op,straddop)

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
		srce=None
		for e in srctree.expressions:
			if e.equals(fa.srce):
				srce=e
		if srce==None:
			raise Exception("Expression doesn't exist")
		opnum=fa.opnum
		addop=self.parseAddOp(fa.addop,srce)
		srce.userSplit(op=opnum,adop=addop)
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
			t.rchildline=self.create_line(self.rx+x1,self.ry+y1,self.rx+x2,self.ry+y2,fill="red")
		else:
			self.coords(t.rchildline,self.rx+x1,self.ry+y1,self.rx+x2,self.ry+y2)
		x1=px+t.width/2
		x2=lpx+t.lchild.width/2
		y2=lpy
		if t.lchildline==None:
			t.lchildline=self.create_line(self.rx+x1,self.ry+y1,self.rx+x2,self.ry+y2,fill="red")
		else:
			self.coords(t.lchildline,self.rx+x1,self.ry+y1,self.rx+x2,self.ry+y2)
		self.drawLines(t.rchild)
		self.drawLines(t.lchild)

	def save(self,fname):
		writeTreeToFile(self.top,fname,append=False,result=userpredictions[self.guiparent.userprediction])

	#Tries to load the file, first by trying if its an action file, then if it is an arguement file
	def load(self,fname,offset=None):
		#check if things have been saved before erasing existing tree
		oldtop=self.top
		oldopnum=gopnum[0]
		gopnum[0]=1
		self.top=TruthTreeMake(total=self,guiparent=self)
		if offset==None:
			try:
				self.loadActionFile(fname)
				self.reset(oldtop)
				self.enterNormalState()
				return fname
			except Exception, e:
				pass
		try:
			self.loadArguementFile(fname,offset)
			self.reset(oldtop)
			self.enterNormalState()
			return
		except Exception, e:
			pass
		#Make this a pop up
		self.top=oldtop
		gopnum[0]=oldopnum
		print "Invalid File"

	def loadActionFile(self,fname):
		actionreader=TruthTreeReader(fname)
		self.intialize(actreader=actionreader)

	def loadArguementFile(self,fname,offset=None):
		if offset!=None:
			reader=OffsetLogicReader(fname,offset,constructors)
		else:
			reader=LogicReader(fname,constructors)
		self.intialize(argreader=reader)

	def reset(self,top):
		self.delete(ALL)
		self.rx=0
		self.ry=0
		self.dx=0
		self.dy=0
		self.mx=0
		self.my=0
		if top==None:
			return
		top.place_forget()
		if not top.isLeaf():
			self.reset(top.rchild)
			self.reset(top.lchild)

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
		self.labels={}
		self.buttons=[]
		self.bound=None
		self.maxWidth=None
		self.rchildline=None
		self.lchildline=None
		self.endinglabel=None
		self.textbox=None
		
	def getTotal(self):
		t=self
		while t.parent!=None:
			t=t.parent
		return t.total

	#Adds empty children to the tree section
	def addChildren(self,ten=False,):
		self.rchild=TruthTreeMake(self,ten,guiparent=self.guiparent)
		self.lchild=TruthTreeMake(self,ten,guiparent=self.guiparent)

	def toList(self):
		if self.isLeaf():
			return [self]
		return [self]+self.rchild.toList()+self.lchild.toList()

	def normalState(self):
		self.removeTextbox()
		self.resetVariables()
		self.updateText()
		self.addOpenCloseButtons()

	def removeEmptyChildren(self):
		if not self.isLeaf():
			if len(self.rchild.expressions)==0 and len(self.lchild.expressions)==0:
				self.guiparent.delete(self.rchildline)
				self.guiparent.delete(self.lchildline)
				self.rchildline=None
				self.lchildline=None
				self.rchild.destroy()
				self.lchild.destroy()
				self.rchild=None
				self.lchild=None

			else:
				self.rchild.removeEmptyChildren()
				self.lchild.removeEmptyChildren()

	def editState(self):
		self.resetVariables()
		self.updateText()
		self.addEditButtons()	

	def updateText(self):
		for i,e in enumerate(self.expressions):
			w=self.guiparent.font.measure(e.toString(outside=True))
			self.height+=self.guiparent.font.metrics("linespace")+4
			if w>self.width:
				self.width=w
			if not e in self.labels.keys():
				l=ExpressionLabel(self,e)
			else:
				l=self.labels[e]
				l.updateText()
			l.grid(row=i,padx=0,pady=0,columnspan=2)
			self.labels[e]=l
		if self.isLeaf() and (self.open or self.closed):
			if self.endinglabel==None:
				if self.open:
					t='O '+str(self.opnum)
				if self.closed:
					t='X '+str(self.opnum)
				w=self.guiparent.font.measure(t)
				self.height+=self.guiparent.font.metrics("linespace")+4
				l=Label(self,text=t,background='white',font=self.guiparent.font)
				if w>self.width:
					self.width=w
				l.grid(row=len(self.labels),padx=0,pady=0,columnspan=2)
				self.endinglabel=l
			else:
				self.endinglabel.grid(row=len(self.labels),padx=0,pady=0,columnspan=2)
		self.width+=2*self.guiparent.borderwidth
		self.height+=2*self.guiparent.borderwidth

	def addOpenCloseButtons(self):
		if self.isLeaf() and not self.open and not self.closed:
			xw=self.guiparent.buttonfont.measure('X')+10
			ow=self.guiparent.buttonfont.measure('O')+10
			h=self.guiparent.buttonfont.metrics("linespace")+10
			closebutton=ButtonWrapper(self,'X',self.guiparent.buttonfont,xw,h)
			closebutton.grid(row=len(self.labels),column=0,padx=0,pady=0,)
			closebutton.bind("<Button-1>",self.closeEvent)
			openbutton=ButtonWrapper(self,'O',self.guiparent.buttonfont,ow,h)
			openbutton.grid(row=len(self.labels),column=1,padx=0,pady=0,)
			openbutton.bind("<Button-1>",self.openEvent)
			self.buttons=[closebutton,openbutton]
			w=xw+ow+8
			if w>self.width:
				self.width=w
			self.height+=h+4

	def closeEvent(self,event):
		self.setClosed()
		self.guiparent.enterNormalState()

	def openEvent(self,event):
		self.setOpen()
		self.guiparent.enterNormalState()

	def addEditButtons(self):
		if self.isLeaf() and not self.open and not self.closed:
			w=0
			r=len(self.labels)
			if self.textbox!=None:
				r+=1
				if 300>self.width:
					self.width=300
					self.height+=34
			c=0
			childw=0
			exprw=self.guiparent.buttonfont.measure('Add Expression')+20
			h=self.guiparent.buttonfont.metrics("linespace")+10
			if len(self.expressions)>=1:
				childw=self.guiparent.buttonfont.measure('Add Children')+20
				addChildrenbutton=ButtonWrapper(self,'Add Children',self.guiparent.buttonfont,childw-15,h-10)
				addChildrenbutton.grid(row=r,column=c,padx=0,pady=0)
				c+=1
				addChildrenbutton.bind("<Button-1>",self.addChildrenEvent)
				self.buttons.append(addChildrenbutton)
			addExpressionbutton=ButtonWrapper(self,'Add Expression',self.guiparent.buttonfont,exprw-15,h-10)
			addExpressionbutton.grid(row=r,column=c,padx=0,pady=0)
			addExpressionbutton.bind("<Button-1>",self.addExpressionEvent)
			self.buttons.append(addExpressionbutton)
			w+=childw+exprw+8
			if w>self.width:
				self.width=w
			self.height+=h+4

	def addExpressionEvent(self,event):
		if self.textbox==None:
			self.guiparent.top.removeTextbox()
			self.textbox=EntryWrapper(self,300,34,self.guiparent.font)
			self.textbox.grid(row=len(self.labels),columnspan=2,padx=2,pady=2)
			self.textbox.bind('<Return>',self.addExpressionEvent)
			self.guiparent.enterEditState()
		else:
			try:
				e=self.guiparent.stringreader.parseString(self.textbox.get())
				self.expressions.append(e)
				self.guiparent.addDestEPair(e,self)
				self.guiparent.top.removeTextbox()
				self.guiparent.enterEditState()
			except Exception, ex:
				if self.textbox.get()!="":
					print "Invalid Expression"
				self.removeTextbox()
	
	def removeTextbox(self):
		if not self.isLeaf():
			self.rchild.removeTextbox()
			self.lchild.removeTextbox()
		if self.textbox!=None:
			self.textbox.grid_remove()
			self.textbox=None

	def addChildrenEvent(self,event):
		self.removeTextbox()
		self.addChildren()
		self.guiparent.enterEditState()

	def computePosition(self):
		xmin,xmax=self.getBounds()
		if self.position!=None:
			return self.position
		if self.isLeaf():
			x=(xmax+xmin-self.width)/2
		else:
			lw=self.lchild.getMaxWidth()
			rw=self.rchild.getMaxWidth()
			if(rw+lw+self.guiparent.wpadding>self.width):
				x=(xmax+xmin+lw-rw-self.width)/2
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
		if self.parent.lchild==self:
			c=(wmax+wmin-self.getMaxWidth()-self.guiparent.wpadding-self.parent.lchild.getMaxWidth())/2
			self.bound=(c,c+self.getMaxWidth())
		if self.parent.rchild==self:
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
		for e in self.labels.keys():
			self.labels[e].grid_remove()
		for b in self.buttons:
			b.grid_remove()
		self.buttons=[]
		if self.endinglabel!=None:
			self.endinglabel.grid_remove()

class ExpressionLabel(Label):
	def __init__(self,parent,expr):
		self.guiparent=parent
		self.expr=expr
		Label.__init__(self,parent,text=self.expr.toString(outside=True),background="white",font=self.guiparent.guiparent.font)
		self.bind("<Button-1>",self.pressed)
		self.selected=False

	def pressed(self,event):
		if not self.expr.canUserSplit():
			print "Can't Split"
		else:
			if not self.selected:
				self.guiparent.guiparent.setSelectedExpression(self)
				self.config(background="Red")
				self.selected=True
			else:
				self.guiparent.guiparent.setSelectedExpression(None)
				self.config(background="White")
				self.selected=False

	def noLongerSelected(self):
		self.config(background="White")
		self.selected=False

	def updateText(self):
		self.config(text=self.expr.toString(outside=True))

class EntryWrapper(Frame):
	def __init__(self,parent,w,h,font=None,text=''):
		self.guiparent=parent
		Frame.__init__(self,parent,width=w,height=h,background="blue")
		
		self.entry=Entry(self,font=font)
		self.pack_propagate(False)
		self.entry.pack(fill=BOTH)
		self.entry.delete(0, END)
		self.entry.insert(0, text)

	def get(self):
		return self.entry.get()

	def bind(self,target,event):
		self.entry.bind(target,event)

class ButtonWrapper(Frame):
	def __init__(self,parent,text,font,w,h):
		self.guiparent=parent
		Frame.__init__(self,parent,width=w,height=h,background="blue")
		self.button=Button(self,font=font,text=text)
		self.pack_propagate(False)
		self.button.pack(fill=BOTH)

	def bind(self,target,event):
		self.button.bind(target,event)

class OffsetPopup:
	def __init__(self,parent):
		self.top=Toplevel(parent)
		l=Label(self.top,text='Enter Question Number:')
		l.pack()
		self.e=EntryWrapper(self.top,200,34,font=parent.font)
		self.e.pack()
		b=ButtonWrapper(self.top,'Submit',parent.buttonfont,100,34)
		b.pack()
		self.e.bind('<Return>',self.submit)
		b.bind('<Button-1>',self.submit)
		self.offset=None
		self.e.focus_set()
	
	def submit(self,event):
		try:
			self.offset=int(self.e.get())
		except Exception, e:
			self.offset=None
		self.top.destroy()

def main():
	root = Tk()
	tree=TreeWindow(root,w=900,h=900)
	root.mainloop()
