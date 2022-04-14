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

# TODO improve speed of execution. Too slow
def cumulative(s, d, r, b):
	constraints = []

	for j in range(len(s)):
		my_sum = Sum([])
		
		for i in range(len(s)):
			my_sum += If(And(i!=j,s[i] <= s[j], s[j] < s[i] + d[i]),r[i],0)
		
		constraints += [ 
			b >= r[j] + my_sum
		]

	return constraints