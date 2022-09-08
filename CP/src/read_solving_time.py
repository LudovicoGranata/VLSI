import os

out_dir = "./CP/out/base/v1"

solved = 0
avg_time = 0.0

for file in os.listdir(out_dir):
	with open(os.path.join(out_dir, file), 'r') as f:
		try:
			last_line = float(f.readlines()[-1])
			float(last_line)
		except:
			continue
		solved += 1
		avg_time += last_line

print(f"Solved {solved}/40 instances")
print(f"Average solving time: {avg_time/solved}s")
