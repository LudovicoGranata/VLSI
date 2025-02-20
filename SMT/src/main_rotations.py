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

def save_solution(instance_idx, grid_width, reached_height, n_circuits, block_widths, block_heights, block_pos_x, block_pos_y, block_rotated):
	with open(f'./SMT/out/rotation/out-{instance_idx}.txt', 'w') as f_result:
		f_result.write(f'{grid_width} {reached_height}\n')
		f_result.write(f'{n_circuits}\n')
		for i in range(n_circuits):
			f_result.write(f'{block_widths[i]} {block_heights[i]} {block_pos_x[i]} {block_pos_y[i]}')
			if block_rotated[i]:
				f_result.write(' R')
			f_result.write('\n')

def solve_task(ins_index):
	
	width, n_circuits, dim1, dim2 = read_task(ins_index)

	# ====================================================
	# ================ DECISION VARIABLES ================
	# ====================================================

	X_pos = [Int(f"X_pos_{i+1}") for i in range(n_circuits)]
	Y_pos = [Int(f"Y_pos_{i+1}") for i in range(n_circuits)]
	rotated = [Bool(f"rotated_{i+1}") for i in range(n_circuits)]

	height = Int("height")

	constraints = []

	# ====================================================
	# ================ MODEL CONSTRAINTS =================
	# ====================================================

	hor_dim = [Int(f"hor_dim_{i+1}") for i in range(n_circuits)]
	ver_dim = [Int(f"ver_dim_{i+1}") for i in range(n_circuits)]

	constraints += [ And(	
		Implies(
			rotated[i],
			And( dim1[i] == ver_dim[i], dim2[i] == hor_dim[i]) ),
		Implies(
			Not(rotated[i]),
			And(dim1[i] == hor_dim[i], dim2[i] == ver_dim[i]) )
	) for i in range(n_circuits)]
	
	configuration.add("largest block on bottom left")
	largest_block_index = np.argmax([dim1[i]*dim2[i] for i in range(n_circuits)])
	constraints += [ And(
						X_pos[largest_block_index] == 0,
						Y_pos[largest_block_index] == 0 )]
	
	configuration.add("diffn")
	constraints += diffn(X_pos, Y_pos, hor_dim, ver_dim)
	
	configuration.add("border constraints")
	constraints += [ And(0 <= X_pos[i], X_pos[i] + hor_dim[i] <= width,
						0 <= Y_pos[i], Y_pos[i] + ver_dim[i] <= height)
						for i in range(n_circuits) #if i != largest_block_index
					]
	
	# ================ Implied constraints =============== => slower
	# configuration.add("cumulative")
	# constraints += cumulative(X_pos, hor_dim, ver_dim, height)
	# constraints += cumulative(Y_pos, ver_dim, hor_dim, width)
	
	# ============== S.B. on x and y axis ================ => slower
	# configuration.add("x and y symmetry with lex order")
	# X_pos_sym = [Int(f"X_pos_sym_{i+1}") for i in range(n_circuits)]
	# Y_pos_sym = [Int(f"Y_pos_sym_{i+1}") for i in range(n_circuits)]

	# constraints += [ And(
	# 	Y_pos_sym[i] == height - Y_pos[i] - ver_dim[i],
	# 	X_pos_sym[i] == width - X_pos[i] - hor_dim[i])
	# 	for i in range(n_circuits)
	# ]

	# =========== S.B. on 2 stacking circuits ============ => slower
	# configuration.add("2 stack vertical constraint")
	# for i in range(n_circuits):
	# 	for j in range(i,n_circuits):
	# 		constraints += [ Implies(
	# 			And(X_pos[i] == X_pos[j], hor_dim[i] == hor_dim[j],
	# 				(hor_dim[i]+hor_dim[j]) == (max_z3([X_pos[i]+hor_dim[i], X_pos[j]+hor_dim[j]]) - min_z3([X_pos[i],X_pos[j]]))),
	# 			Y_pos[i] < Y_pos[j]
	# 		)]

	opt = Optimize()

	opt.add(constraints)
	opt.minimize(height)
	
	opt.set(timeout=opt_timeout*60*1000)

	X_pos_sol = []
	Y_pos_sol = []
	rotated_sol = []
	
	if opt.check() == sat:
		model = opt.model()
		for i in range(n_circuits):
			X_pos_sol.append(model.evaluate(X_pos[i]).as_string())
			Y_pos_sol.append(model.evaluate(Y_pos[i]).as_string())
			rotated_sol.append(model.evaluate(rotated[i]))
	
		height_sol = model.evaluate(height).as_string()

		print(f"instance - {ins_index}")
		
		save_solution(ins_index, width, int(height_sol), n_circuits, dim1, dim2, X_pos_sol, Y_pos_sol, rotated_sol)

		return 0
	return -1 # -1 error is for timeout

if __name__ == "__main__":
	
	n_instances = 40

	global configuration
	configuration = set()
	global opt_timeout
	opt_timeout = 5 # indicate minutes
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
