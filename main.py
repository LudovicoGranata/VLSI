import datetime

import minizinc
from minizinc import *

def solve_cp():

    Total_instances = 40
    Solved_instances = 0
    Average_time = 0
    gecode = Solver.lookup("gecode")
    for i in range(1, 41):
        print ("trying to solve instance :"+ str(i)+ "...")
        VLSI_model = Model("./VLSI_model.mzn")
        VLSI_model.add_file("./instances/ins-"+str(i)+".dzn")
        instance = Instance(gecode, VLSI_model)
        result = instance.solve(timeout=datetime.timedelta(seconds=3))
        #print(result)
        if result.status == minizinc.result.Status.OPTIMAL_SOLUTION:
            solving_time = ((result.statistics['time'].microseconds / (10 ** 6)) + result.statistics['time'].seconds)
            print("solved instance " + str(i) + " in = " + str (solving_time))
            Solved_instances+=1
            Average_time += solving_time
        else:
            print("instance: "+str(i)+" not solved in the timelimit")
    Average_time = Average_time/Solved_instances
    print ("the average solving time of the solved instances is "+str(Average_time)+ " seconds and the solved instances are "+str(Solved_instances)+"/40" )







if __name__ == '__main__':
    solve_cp()

