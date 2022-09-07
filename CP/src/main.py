import os
import subprocess
from time import time


def solve_instance(cores, model, in_file, out_dir):
	# Run the chosen model
	command = f'minizinc --solver Gecode -p {cores} -t 300000 {model} {in_file}' 

	instance_name = in_file.split('/')[-1] if os.name == 'nt' else in_file.split('/')[-1]
	instance_num = instance_name[4:len(instance_name) - 4]
	out_file = os.path.join(out_dir, "out-"+instance_num+".txt")
	with open(out_file, 'w') as f:
		print(f'{out_file}:', end='\n', flush=True)
		start_time = time()
		subprocess.run(command.split())
		elapsed_time = time() - start_time
		print(f'{elapsed_time * 1000:.1f} ms')
		if (elapsed_time * 1000) < 300000:
			subprocess.run(command.split(), stdout=f)
			f.write('{}'.format(elapsed_time))

def main():	
	models = ["base_model_v1.mzn", 
		"base_model_v2.mzn",
		"base_model_v3.mzn",
		"base_model_v4.mzn",
		"base_model_v5.mzn",
		"base_model_v6.mzn",
		"base_model_v7.mzn",
		"base_model_v8.mzn"]

	cores = 8
	ins_dir = "./CP/ins/"
	out_dir = "./CP/out/base/"
	model_dir = "./CP/src/models/"
	
	for model in models:
		for in_file in os.listdir(ins_dir):
			solve_instance(cores, f"{model_dir}{model}", f"{ins_dir}{in_file}", out_dir)

if __name__ == '__main__':
	main()
	