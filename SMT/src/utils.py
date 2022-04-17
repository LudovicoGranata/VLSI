from z3 import *

def max_z3(vars):
    max = vars[0]
    for v in vars[1:]:
        max = If(v > max, v, max)
    return max

def min_z3(vars):
    min = vars[0]
    for v in vars[1:]:
        min = If(v < min, v, min)
    return min

def diffn(x, y, dx, dy):	
	constraints = []

	for i in range(len(x)):
		for j in range(i+1, len(x)):
			constraints += [ Or(
				x[i] + dx[i] <= x[j], y[i] + dy[i] <= y[j],
				x[j] + dx[j] <= x[i], y[j] + dy[j] <= y[i]
			)]
	
	return constraints

def cumulative(s, d, r, b):
	constraints = []

	for j in range(len(s)):
			
		my_sum = Sum([ If(And(i!=j,s[i] <= s[j], s[j] < s[i] + d[i]), r[i], 0) for i in range(len(s))])
		constraints += [ 
			b >= r[j] + my_sum
		]

	return constraints

def lex_lesseq(x, y):
	constraints = []

	constraints += [ x[0] <= y[0] ]
	
	for i in range(1, len(x)):
		constraints += [ Implies(
			And([ x[j] == y[j] for j in range(i) ]) ,
			x[i] <= y[i]) ]

	return constraints