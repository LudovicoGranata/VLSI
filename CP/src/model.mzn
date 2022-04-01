include "globals.mzn";

int: n_circuits;   % Number of tasks
set of int: CIRCUITS = 1..n_circuits;  

int: width;   % Number of resources
set of int: WIDTH = 0..width; 
array[CIRCUITS, 1..2] of int: coordinates; %Resource requirements of tasks


 int:k = sum([coordinates[n,2] | n in CIRCUITS]);
array[CIRCUITS] of var 0..k: start; %Variables for task start times

%resource constraints
constraint cumulative(start, [coordinates[n,2]| n in CIRCUITS], [coordinates[n,1] | n in CIRCUITS] , width) ::domain;

%makespan as objective function
var int: makespan = max(t in CIRCUITS)(start[t] + coordinates[t,2]);

%for LNS
include "gecode.mzn";

solve 
 :: restart_luby(250) 
 minimize makespan;


