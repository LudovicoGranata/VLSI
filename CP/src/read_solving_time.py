import os

out_dir = "./CP/out/base/v1"

solved = 0
avg_time = 0.0

for file in os.listdir(out_dir):
	with open(file, 'r') as f:
		last_line = f.readlines()[-1]
		try:
			float(last_line)
		except ValueError:
			continue
		solved += 1
		avg_time += float(last_line)

print(f"Solved {solved}/40 instances")
print(f"Average solving time: {avg_time/solved}s")
