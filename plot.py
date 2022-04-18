import matplotlib.pyplot as plt

def get_cmap(n, name = 'hsv'):
  return plt.cm.get_cmap(name, n)

def plot(dir, instance, out):
  # Removing X and Y margins:
  plt.rcParams['axes.xmargin'] = 0
  plt.rcParams['axes.ymargin'] = 0

  # Preparing a new figure for plotting:
  plt.figure(figsize=(8, 8))
  plt.title(f'Solution for: "{instance}"')
  plt.grid(visible=True, linestyle='-')
  plt.axis("scaled")

  ax = plt.gca()
  cmap = None

  i=0
  with open(dir + "/"+ instance,'r') as readfile:
    for line in readfile:
      line = line.replace("\n","")
      if (i==0):
        width, height = line.split()

        # Setting correct ranges and ticks for X and Y axes:
        plt.xlim((0, int(width)))
        plt.ylim((0, int(height)))
        plt.xticks([n for n in range(int(width) + 1)])
        plt.yticks([n for n in range(int(height) + 1)])

        #canvas = plt.Rectangle((0,0), width=int(width), height=int(height), facecolor="none", edgecolor="black")
        #ax.add_patch(canvas)
      elif (i==1):
        n_circuits = int(line)
        cmap = get_cmap(n_circuits)
      else:
        # Building a rectangle based on information specified in the instance solution:
        c_width, c_height, c_bottom_left_x, c_bottom_left_y =  line.split()
        circuit = plt.Rectangle((int(c_bottom_left_x), int(c_bottom_left_y)),
          width=int(c_width), height=int(c_height),
          facecolor=cmap(i-2), edgecolor="black", linewidth=3)
        
        # Adding a text annotation to each rectangle:
        ax.add_artist(circuit)
        rx, ry = circuit.get_xy()
        cx = rx + circuit.get_width()/2.0
        cy = ry + circuit.get_height()/2.0
        ax.annotate(f'{i-2}', (cx, cy), color='w', weight='bold', fontsize=16, ha='center', va='center')
        
        # Effectively adding the rectangle to the plot:
        ax.add_patch(circuit)
      i += 1

  # Here we export the plot:
  plt.savefig(out+"/"+instance.split(".")[0]+"_out.png")
  
  # Each figure must be explicitly closed to avoid
  # unnecessarily consuming too much memory (and
  # causing a related RuntimeWarning):
  plt.close()
