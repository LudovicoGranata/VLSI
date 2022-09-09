import os
import subprocess
from time import time


def solve_instance(cores, model, in_file, out_dir):
	# Run the chosen model
	command = f'minizinc --solver Gecode -p {cores} -t 300000 {model} {in_file}' 

	instance_name = in_file.split('/')[-1] if os.name == 'nt' else in_file.split('/')[-1]
	instance_num = instance_name[4:len(instance_name) - 4]

	# if (int(instance_num) not in [5,8,10,12,14]): return
	
	out_file = os.path.join(out_dir, "out-"+instance_num+".txt")
	with open(out_file, 'w') as f:
		print(f'{out_file}:', end='\n', flush=True)
		
		start_time = time()
		subprocess.run(command.split())
		elapsed_time = time() - start_time
		
		print(f'{elapsed_time:4f} s')
		if (elapsed_time * 1000) < 300000:
			subprocess.run(command.split(), stdout=f)

def main():
	models = ["rotation_model.mzn"]
	out_dir_models = [""]

	cores = 8
	ins_dir = "./CP/ins/"
	out_dir = "./CP/out/rotation/"
	model_dir = "./CP/src/models/"
	
	for model, out_dir_model in zip(models, out_dir_models):
		for in_file in os.listdir(ins_dir):
			solve_instance(cores, f"{model_dir}{model}", f"{ins_dir}{in_file}", f"{out_dir}{out_dir_model}")

if __name__ == '__main__':
	main()
