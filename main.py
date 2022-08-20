import datetime
import minizinc as mz
import plot


def solve_cp(model_path):
    Total_instances = 40
    Solved_instances = 0
    Average_time = 0
    gecode = mz.Solver.lookup("gecode")

    for i in range(1, Total_instances + 1):
        print(f">>> Trying to solve instance #{i}...")
        VLSI_model = mz.Model(model_path)
        VLSI_model.add_file("./CP/ins/ins-"+str(i)+".dzn")
        instance = mz.Instance(gecode, VLSI_model)
        result = instance.solve(timeout=datetime.timedelta(seconds=300))
        #print(result)
        if result.status == mz.result.Status.OPTIMAL_SOLUTION:
            solving_time = ((result.statistics['time'].microseconds / (10 ** 6)) + result.statistics['time'].seconds)
            print("solved instance " + str(i) + " in = " + str(round(solving_time, 3)))
            Solved_instances+=1
            Average_time += solving_time
            with open('./CP/out/ins-' + str(i) + '.txt', 'w') as writefile:
                writefile.write(str(result))
            plot.plot("./CP/out/","ins-"+str(i)+".txt","./CP/out/images")
        else:
            print("instance: "+str(i)+" not solved in the timelimit")
    if Solved_instances!=0:
        Average_time = Average_time/Solved_instances
        print ("the average solving time of the solved instances_cp is "+str(Average_time)+ " seconds and the solved instances_cp are "+str(Solved_instances)+"/40" )
    else:
        print("no instance solved")


if __name__ == '__main__':
    solve_cp("./CP/src/rotation_model.mzn")
    