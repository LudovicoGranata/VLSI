import matplotlib.pyplot as plt

def get_cmap(n, name = 'hsv'):
  return plt.cm.get_cmap(name, n)

def plot(dir, instance, out):
  ax = plt.gca()
  cmap = None

  i=0
  with open(dir + "/"+ instance,'r') as readfile:
    for line in readfile:
      line = line.replace("\n","")
      if (i==0):
        width, height = line.split()
        canvas = plt.Rectangle ( (0,0), width=int(width), height=int(height), facecolor= "none", edgecolor="black")
        ax.add_patch(canvas)
      if (i==1):
        n_circuits = int(line)
        cmap = get_cmap(n_circuits)

      if(i>1):
        c_width, c_height, c_bottom_left_x, c_bottom_left_y =  line.split()
        circuit = plt.Rectangle ( (int(c_bottom_left_x),int(c_bottom_left_y)), width=int(c_width), height=int(c_height), facecolor= cmap(i-2), edgecolor="black")
        ax.add_patch(circuit)
      i += 1

  plt.axis("scaled")
  plt.savefig(out+"/"+instance.split(".")[0]+"_out.png")
  #plt.show()