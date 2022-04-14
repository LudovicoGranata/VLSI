import numpy as np
from z3 import *
from utils import *
import time

def read_task(ins_index):
	hor_dim = []
	ver_dim = []
	
	with open(f'./SMT/ins/ins-{ins_index}.txt', mode='r', encoding='UTF8') as f_inst:
		width = int(f_inst.readline().replace('\n', ''))
		n_circuits = int(f_inst.readline().replace('\n', ''))

		for i in range(n_circuits):
			coordinates = f_inst.readline().replace("\n", "").split()
			hor_dim.append(int(coordinates[0]))
			ver_dim.append(int(coordinates[1]))

	return width, n_circuits, hor_dim, ver_dim

def solve_task(ins_index):
	width, n_circuits, hor_dim, ver_dim = read_task(ins_index)

	circuitx = [Int(f"circuitx_{i+1}") for i in range(n_circuits)]
	circuity = [Int(f"circuity_{i+1}") for i in range(n_circuits)]

	height = Int("height")

	max_height = sum(ver_dim)

	constraints = []

	# define circuitx and circuity domains
	constraints += [ And(0 <= circuitx[i], circuitx[i] <= width - min(hor_dim)) for i in range(n_circuits) ]
	constraints += [ And(0 <= circuity[i], circuity[i] <= max_height - min(ver_dim)) for i in range(n_circuits) ]

	# circuits inside width and height constraint
	constraints += [ And(circuitx[i] + hor_dim[i] <= width) for i in range(n_circuits)]
	constraints += [ And(circuity[i] + ver_dim[i] <= height) for i in range(n_circuits)]

	# no overlap constraint
	constraints += diffn(circuitx, circuity, hor_dim, ver_dim)

	# cumulative constraint => slower
	constraints += cumulative(circuitx, hor_dim, ver_dim, height)
	constraints += cumulative(circuity, ver_dim, hor_dim, width)

	opt = Optimize()
	opt.add(constraints)
	opt.minimize(height)
	
	circuitx_sol = []
	circuity_sol = []
	
	if opt.check() == sat:
		model = opt.model()
		for i in range(n_circuits):
			circuitx_sol.append(model.evaluate(circuitx[i]).as_string())
			circuity_sol.append(model.evaluate(circuity[i]).as_string())
	
		height_sol = model.evaluate(height).as_string()

		print(f"instance - {ins_index}")
		print(circuitx_sol)
		print(circuity_sol)
		print(height_sol)

if __name__ == "__main__":
	start_time = time.time()
	
	for i in range (1,11):
		solve_task(i)

	print("--- %s seconds ---" % (time.time() - start_time))