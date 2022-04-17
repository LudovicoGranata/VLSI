from z3 import *
from utils import *
import time
import numpy as np

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

	# ====================================================
	# ================ DECISION VARIABLES ================
	# ====================================================

	circuitx = [Int(f"circuitx_{i+1}") for i in range(n_circuits)]
	circuity = [Int(f"circuity_{i+1}") for i in range(n_circuits)]

	height = Int("height")

	constraints = []

	# ====================================================
	# ================ MODEL CONSTRAINTS =================
	# ====================================================

	configuration.add("border constraints")
	constraints += [ And(0 <= circuitx[i], circuitx[i] + hor_dim[i] <= width,
						0 <= circuity[i], circuity[i] + ver_dim[i] <= height)
						for i in range(n_circuits) #if i != largest_block_index
					]
	
	configuration.add("diffn")
	constraints += diffn(circuitx, circuity, hor_dim, ver_dim)
	
	# ================ Implied constraints ===============
	# configuration.add("cumulative")
	# constraints += cumulative(circuitx, hor_dim, ver_dim, height)
	# constraints += cumulative(circuity, ver_dim, hor_dim, width)
	

	# ====================================================
	# ========== SYMMETRY BREAKING CONSTRAINTS ===========
	# ====================================================
	
	# ============= Largest circuit on (0,0) ============= => slower
	# configuration.add("largest block on bottom left")
	# largest_block_index = np.argmax([hor_dim[i]*ver_dim[i] for i in range(n_circuits)])
	# constraints += [ And(
	# 					circuitx[largest_block_index] == 0,
	# 					circuity[largest_block_index] == 0 )]

	# ============== S.B. on x and y axis ================ => slower
	# configuration.add("x and y symmetry with lex order")
	# circuitx_sym = [Int(f"circuitx_sym_{i+1}") for i in range(n_circuits)]
	# circuity_sym = [Int(f"circuity_sym_{i+1}") for i in range(n_circuits)]

	# constraints += [ And(
	# 	circuity_sym[i] == height - circuity[i] - ver_dim[i],
	# 	circuitx_sym[i] == width - circuitx[i] - hor_dim[i])
	# 	for i in range(n_circuits)
	# ]

	# =========== S.B. on 2 stacking circuits ============ => slower
	# configuration.add("2 stack vertical constraint")
	# for i in range(n_circuits):
	# 	for j in range(i,n_circuits):
	# 		constraints += [ Implies(
	# 			And(circuitx[i] == circuitx[j], hor_dim[i] == hor_dim[j],
	# 				(hor_dim[i]+hor_dim[j]) == (max_z3([circuitx[i]+hor_dim[i], circuitx[j]+hor_dim[j]]) - min_z3([circuitx[i],circuitx[j]]))),
	# 			circuity[i] < circuity[j]
	# 		)]

	opt = Optimize()

	opt.add(constraints)
	opt.minimize(height)
	
	opt.set(timeout=opt_timeout*60*1000)

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
		# print(opt.assertions)

		return 0
	return -1 # -1 error is for timeout

if __name__ == "__main__":
	
	n_instances = 40

	global configuration
	configuration = set()
	global opt_timeout
	opt_timeout = 1 # indicate minutes
	solved = 0
	failed_instances = []
	start_time = time.time()
	
	for i in range (1,n_instances+1):
		start = time.time()
		result = solve_task(i)
		if result == 0:
			print("--- {:.5f} seconds ---".format(time.time() - start))
			solved += 1
		elif result == -1:
			print(f"instance - {i} FAILED => Timeout")
			failed_instances.append(i)
		print()


	print("Configuration:")
	for e in configuration:
		print(f"\t- {e}")
	print(f"Timeout: {opt_timeout} minutes")
	print(f"Solved instances: {solved}/{n_instances}")
	print("Total time: {:.5f} seconds".format(time.time() - start_time))
	print(f"Failed instances: {failed_instances}")