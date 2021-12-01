import datetime

# For CP solving:
import minizinc as mz

# For SAT solving:
from sat_utils import *
import plot

def solve_cp():
    Total_instances = 40
    Solved_instances = 0
    Average_time = 0
    gecode = mz.Solver.lookup("gecode")
    for i in range(1, 41):
        print ("trying to solve instance :"+ str(i)+ "...")
        VLSI_model = mz.Model("./VLSI_model.mzn")
        VLSI_model.add_file("./instances_cp/ins-"+str(i)+".dzn")
        instance = mz.Instance(gecode, VLSI_model)
        result = instance.solve(timeout=datetime.timedelta(seconds=30))
        #print(result)
        if result.status == mz.result.Status.OPTIMAL_SOLUTION:
            solving_time = ((result.statistics['time'].microseconds / (10 ** 6)) + result.statistics['time'].seconds)
            print("solved instance " + str(i) + " in = " + str (solving_time))
            Solved_instances+=1
            Average_time += solving_time
            with open('./out_cp/ins-' + str(i) + '.txt', 'w') as writefile:
                writefile.write(str(result))
            plot.plot("./out_cp","ins-"+str(i)+".txt","./out_cp/images")
        else:
            print("instance: "+str(i)+" not solved in the timelimit")
    Average_time = Average_time/Solved_instances
    print ("the average solving time of the solved instances_cp is "+str(Average_time)+ " seconds and the solved instances_cp are "+str(Solved_instances)+"/40" )

def solve_SAT():
    create_solver_from_instance('./instances_SAT/ins-1.txt')


if __name__ == '__main__':
    solve_cp()
    #solve_SAT()

