import datetime
import minizinc as mz

def solve_cp(model_path):
	tot_instances = 40
	solved_instances = 0
	avg_time = 0
	gecode = mz.Solver.lookup("gecode")

	for i in range(1, tot_instances + 1):

		print(f"Instance {i}/{tot_instances}")

		VLSI_model = mz.Model(model_path)
		VLSI_model.add_file("./CP/ins/ins-"+str(i)+".dzn")
		instance = mz.Instance(gecode, VLSI_model)
		
		result = instance.solve(timeout = datetime.timedelta(seconds=300), # 5 min timeout
								processes = 8,
								optimisation_level = 1)
		
		print(result)

		if result.status == mz.result.Status.OPTIMAL_SOLUTION:
			solved_instances+=1
			
			solving_time = ((result.statistics['time'].microseconds / (10 ** 6)) + result.statistics['time'].seconds)
			avg_time += solving_time
			print("Solved!")
			print(f"Elapsed time: {str(round(solving_time, 3))}")
			
			with open('./CP/out/base/out-' + str(i) + '.txt', 'w') as writefile:
				writefile.write(str(result))
		else:
			print("Timeout!")
		
		print()
	
	if solved_instances!=0:
		avg_time = avg_time/solved_instances
		print(f"Solved instances: {str(solved_instances)}/{tot_instances}")
		print(f"Average solving time: {str(avg_time)}s")
	else:
		print("No instances solved :(")


if __name__ == '__main__':
	solve_cp("./CP/src/models/base_model_v1.mzn")
	