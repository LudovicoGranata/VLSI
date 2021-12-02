import matplotlib.pyplot as plt

def get_cmap(n, name = 'hsv'):
  return plt.cm.get_cmap(name, n)

def plot(dir, instance, out):
  plt.figure(figsize=(8, 8))
  ax = plt.gca()
  cmap = None

  i=0
  with open(dir + "/"+ instance,'r') as readfile:
    for line in readfile:
      line = line.replace("\n","")
      if (i==0):
        width, height = line.split()
        plt.xticks([n for n in range(int(width) + 1)])
        plt.yticks([n for n in range(int(height) + 1)])
        canvas = plt.Rectangle((0,0), width=int(width), height=int(height), facecolor="none", edgecolor="black")
        ax.add_patch(canvas)
      elif (i==1):
        n_circuits = int(line)
        cmap = get_cmap(n_circuits)
      else:
        c_width, c_height, c_bottom_left_x, c_bottom_left_y =  line.split()
        circuit = plt.Rectangle((int(c_bottom_left_x), int(c_bottom_left_y)), width=int(c_width), height=int(c_height), facecolor=cmap(i-2), edgecolor="black")
        ax.add_patch(circuit)
      i += 1

  plt.axis("scaled")
  plt.savefig(out+"/"+instance.split(".")[0]+"_out.png")