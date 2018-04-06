#! /usr/bin/env python
""" 
#TITLE 
  Pareto Graph Contraction Algorithm 

#AUTHORS
  Philippe NGHE
      ESPCI
      10 rue Vauquelin, 75005 Paris, France
      philippe dot nghe at espci dot fr

  Bela Mulder
      FOM Institute AMOLF
      Science Park 104, 1098 XG Amsterdam, the Netherlands
      mulder at amolf dot nl

#DESCRIPTION 
  Python implementation of the Graph Contraction Algorithm described in 

  Nghe P, Mulder B & Tans SJ,
  "A graph-based algorithm for the multi-objective optimization of gene regulatory networks"
  European Journal of Operational Research (2018)
  
  Default stack implementation Python
  Source: http://interactivepython.org/UhZmZ/courselib/static/pythonds/BasicDS/ImplementingaStackinPython.html

#DATE 
  2009-2018

#Version
  1.0

#LICENSE
  Copyright 2018 Philippe Nghe & Bela Mulder

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at   http://www.apache.org/licenses/LICENSE-2.0.
  Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS,WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.


#COMMENTS
  Modified: added __str__ method for reporting purposes

"""



class Stack:
     def __init__(self):
         self.items = []

     def isEmpty(self):
         return self.items == []

     def push(self, item):
         self.items.append(item)

     def pop(self):
         return self.items.pop()

     def peek(self):
         return self.items[len(self.items)-1]

     def size(self):
         return len(self.items)

     def __str__(self):
     	string = ''
     	for it in self.items:
     		string += str(it)
     	return string

#
# Instruction object used in path counting routine n_path
#

ENTER = 1
LEAVE = -1

class Instruction:

	def __init__(self, op, nd):
		self.op = op
		self.node = nd

	def __str__(self):
		if self.op == ENTER:
			ops = 'ENTER'
		else:
			ops = 'LEAVE'
		return '['+ops+':'+str(self.node)+']'
    
#
# Definition of graph elements
#


MAXIMUM = 2
ASCEND = 1
TRADEOFF = 0
DESCEND = -1
MINIMUM = -2

class Node:
    def __init__(self,vr,st):
        self.vars = vr
        self.state = st

    def __eq__(self,other):
        return (self.vars == other.vars) and (self.state == other.state)

    def __str__(self):
        return '('+str(self.vars)+','+str(self.state)+')'

    def __hash__(self):
        return hash(str(self))
    

FREE = 1
FROZEN = 0

class Edge:
    def __init__(self, nd_i, nd_f, st=None):
        self.node_i = nd_i
        self.node_f = nd_f
        if st is None:
            self.state = 1
        else:
            self.state = st
    
    def __eq__(self,other):
        return (self.node_i == other.node_i) and (self.node_f == other.node_f)
    
    def __str__(self):
        return '('+str(self.node_i)+','+str(self.node_f)+','+str(self.state)+')'
    
    
class Graph:
    def __init__(self, nd_set, edg_set):
        self.node_set = nd_set
        self.edge_set = edg_set
        
    def __str__(self):
        string = ''
        for nd in self.node_set:
            string += str(nd)
        return string


#
# Print lists
#   



def dump_edges(edges):
    for e in edges:
        print(e)

def dump_nodes(nodelist):
    for n in (nodelist):
        print(n)
        
def dump_graphs(graph_set):
    for graph in graph_set:
        print "nodes"
        print(graph)
        print "edges"
        dump_edges(graph.edge_set)
#
# freeze an edge in a graph
#
    
def freeze(ini_node,fin_node,graph):
    new_edges = []
    to_freeze = Edge(ini_node,fin_node)
    to_freeze.state = 0
    for edge in graph.edge_set:
        if edge == to_freeze:
            new_edges.append(to_freeze)
        else:
            new_edges.append(edge)
    return Graph(graph.node_set,new_edges)


#
# Functions for getting successors and predecessors of node in graph
#

def get_successors(node, graph):
    successors = []
    for edge in graph.edge_set:
        if node == edge.node_i:
            successors.append(edge.node_f)
    return successors

def get_predecessors(node,graph):
    predecessors = []
    for edge in graph.edge_set:
        if node == edge.node_f:
            predecessors.append(edge.node_i)
    return predecessors

def get_free_successors(node, graph):
    successors = []
    for edge in graph.edge_set:
        if edge.state and node == edge.node_i:
            successors.append(edge.node_f)
    return successors

def get_free_predecessors(node,graph):
    predecessors = []
    for edge in graph.edge_set:
        if edge.state and node == edge.node_f:
            predecessors.append(edge.node_i)
    return predecessors


#
# Functions to order a list of nodes with ASCENDING and DESCENDING first
#
    
def order_nodes(node_list):
    activenodes = [n for n in node_list if (n.state==1 or n.state==-1)]
    inactivenodes = [n for n in node_list if (n.state!=1 and n.state!=-1)]
    return activenodes+inactivenodes


#
# Perform transitive reduction of graph
#

def transitive_reduction(graph):
	keep_edges = []
	for edge in graph.edge_set:
		if n_paths(edge.node_i,edge.node_f,graph) == 1:
			keep_edges.append(edge)
	return Graph(graph.node_set,keep_edges)


def local_transitive_reduction(graph,node):
    p = get_predecessors(node, graph)
    s = get_successors(node, graph)
    keep_edges = []
    for edge in graph.edge_set:
        if node == edge.node_i and edge.node_f in s:
            if onlyDirectPath(edge.node_i,edge.node_f,graph):
                keep_edges.append(edge)
        elif edge.node_i in p and node == edge.node_f:
            if onlyDirectPath(edge.node_i,edge.node_f,graph):
                keep_edges.append(edge)
        else:
            keep_edges.append(edge)
    return Graph(graph.node_set,keep_edges)

#
# check whether there is at least 1 indirect path between two directly connected nodes
#

#
# Count number of paths between two nodes
#


def n_paths(node_i, node_f, graph):
	numpaths = {}
	visited = {}
	stack = Stack()
	for node in graph.node_set:
		numpaths[node] = 0
		visited[node] = False
	numpaths[node_f] = 1
	stack.push(Instruction(ENTER,node_i))
	step = 0
	while not stack.isEmpty():
		step += 1
		instruction = stack.pop()
		operation = instruction.op
		node = instruction.node
		if operation == ENTER:
			if not visited[node]:
				stack.push(Instruction(LEAVE,node))
				successors = get_successors(node,graph)
				for succ in successors:
					stack.push(Instruction(ENTER,succ))
		else:
			visited[node] == True
			successors = get_successors(node,graph)
			for succ in successors:
				numpaths[node] += numpaths[succ]
	return(numpaths[node_i])
    
    

def onlyDirectPath(a,b,graph):
    cutGraph = Graph(graph.node_set[:],graph.edge_set[:])
    cutGraph.edge_set.remove(Edge(a,b))
    todolist = [a]
    donelist = []
    while todolist:
        node = todolist.pop()
        donelist.append(node)
        successors = get_successors(node,cutGraph)
        for s in successors:
            if s==b:
                return 0
            if s not in donelist:
                todolist.append(s)
    return 1



#
# Collect top-ascenders and bottom-descenders respectively
#

def top_ascenders(graph):
    top_nodes = []
    for node in graph.node_set:
        if node.state == ASCEND:
            predecessors = get_predecessors(node,graph)
            if not any([p.state == ASCEND for p in predecessors]):
                top_nodes.append(node)
    return top_nodes

def bottom_descenders(graph):
    bottom_nodes = []
    for node in graph.node_set:
        if node.state == DESCEND:
            successors = get_successors(node,graph)
            if not any([s.state == DESCEND for s in successors]):
                bottom_nodes.append(node)
    return bottom_nodes

def simple_top_ascenders(graph):
    simple_top_nodes = []
    for node in graph.node_set:
        if node.state == ASCEND:
            predecessors = get_free_predecessors(node,graph)
            if not any([p.state == ASCEND for p in predecessors]) and len(predecessors)==1:
                simple_top_nodes.append(node)
    return simple_top_nodes

def simple_bottom_descenders(graph):
    simple_bottom_nodes = []
    for node in graph.node_set:
        if node.state == DESCEND:
            successors = get_free_successors(node,graph)
            if not any([s.state == DESCEND for s in successors]) and len(successors)==1:
                simple_bottom_nodes.append(node)
    return simple_bottom_nodes


#
# Rules for fusing nodes
#

up_fuse = {MAXIMUM: MAXIMUM,TRADEOFF: TRADEOFF, DESCEND: TRADEOFF}
down_fuse = {ASCEND: TRADEOFF, TRADEOFF: TRADEOFF, MINIMUM: MINIMUM}

def fuse_nodes_up(pred,ascender,graph):
    fused_node = Node(pred.vars+ascender.vars,up_fuse[pred.state])
    new_nodes = [nd for nd in graph.node_set if not ((nd == pred) or (nd == ascender))]
    new_nodes.append(fused_node)
    new_edges = []
    for edge in graph.edge_set:
        source = edge.node_i
        target = edge.node_f
        edgestate = edge.state
        if not ((source == pred) and (target == ascender)):   # discard the edge with the fusing nodes
            if target == pred:
                new_edges.append(Edge(source,fused_node,edgestate))
            elif source == pred:
                new_edges.append(Edge(fused_node,target,edgestate))
            elif source == ascender:
                new_edges.append(Edge(fused_node,target,edgestate))
            elif target == ascender:
                new_edges.append(Edge(source,fused_node,edgestate))
            else:
                new_edges.append(edge)
    return local_transitive_reduction(Graph(new_nodes,new_edges),fused_node)
     


def fuse_nodes_down(descender,succ,graph):
    fused_node = Node(descender.vars+succ.vars,down_fuse[succ.state])
    new_nodes = [nd for nd in graph.node_set if not ((nd == descender) or (nd == succ))]
    new_nodes.append(fused_node)
    new_edges = []
    for edge in graph.edge_set:
        source = edge.node_i
        target = edge.node_f
        edgestate = edge.state
        if not ((source == descender) and (target == succ)):   # discard the edge with the fusing nodes
            if target == succ:
                new_edges.append(Edge(source,fused_node,edgestate))
            elif source == succ:
                new_edges.append(Edge(fused_node,target,edgestate))
            elif source == descender:
                new_edges.append(Edge(fused_node,target,edgestate))
            elif target == descender:
                new_edges.append(Edge(source,fused_node,edgestate))
            else:
                new_edges.append(edge)
    return local_transitive_reduction(Graph(new_nodes,new_edges),fused_node)




#
# Calculate recusively the set of terminal graphs by succesive reduction
#

def pareto_optimize_test(graph,depth):
    print depth
    print (graph)
    direction = 0
    simple_top = simple_top_ascenders(graph)
    if simple_top:
        to_fuse = simple_top[0]
        direction = 1
    else:
        simple_bottom = simple_bottom_descenders(graph)
        if simple_bottom:
            to_fuse = simple_bottom[0]
            direction = -1
        else:
            tops = top_ascenders(graph)
            if tops:
                to_fuse = tops[0]
                direction = 1
            else:
                bottoms = bottom_descenders(graph)
                if bottoms:
                    to_fuse = bottoms[0]
                    direction = -1
    contracted_graph_set = []
    if direction==1:
        predecessors = order_nodes(get_free_predecessors(to_fuse,graph))
        for p in predecessors:
            contracted_graph_set.append(fuse_nodes_up(p,to_fuse,graph))
            graph = freeze(p,to_fuse,graph)
    elif direction==-1:
        successors = order_nodes(get_free_successors(to_fuse,graph))
        for s in successors:
            contracted_graph_set.append(fuse_nodes_down(to_fuse,s,graph))
            graph = freeze(to_fuse,s,graph)
    for contracted_graph in contracted_graph_set:
        pareto_optimize_test(contracted_graph,depth+1)


def pareto_optimize(graph):
    direction = 0
    simple_top = simple_top_ascenders(graph)
    if simple_top:
        to_fuse = simple_top[0]
        direction = 1
    else:
        simple_bottom = simple_bottom_descenders(graph)
        if simple_bottom:
            to_fuse = simple_bottom[0]
            direction = -1
        else:
            tops = top_ascenders(graph)
            if tops:
                to_fuse = tops[0]
                direction = 1
            else:
                bottoms = bottom_descenders(graph)
                if bottoms:
                    to_fuse = bottoms[0]
                    direction = -1
                else:
                    return [graph]
    contracted_graph_set = []
    terminal_graph_set = []
    if direction==1:
        predecessors = order_nodes(get_free_predecessors(to_fuse,graph))
        for p in predecessors:
            contracted_graph_set.append(fuse_nodes_up(p,to_fuse,graph))
            graph = freeze(p,to_fuse,graph)
    elif direction==-1:
        successors = order_nodes(get_free_successors(to_fuse,graph))
        for s in successors:
            contracted_graph_set.append(fuse_nodes_down(to_fuse,s,graph))
            graph = freeze(to_fuse,s,graph)
    for contracted_graph in contracted_graph_set:
        terminal_graph_set = terminal_graph_set+pareto_optimize(contracted_graph)
    return terminal_graph_set



#example
mx = Node([0], MAXIMUM)
a =  Node([1], TRADEOFF)
b = Node([2],ASCEND)
c =  Node([3], DESCEND)
d =  Node([4], TRADEOFF)
mn = Node([5],MINIMUM)
nodes = [mx,a,b,c,d,mn]
edges = [Edge(mx,a),Edge(mx,c),Edge(a,b),Edge(c,b),Edge(c,d),Edge(d,mn),Edge(b,mn)]
G = Graph(nodes,edges)
P = pareto_optimize(G)
dump_graphs(P)




	
