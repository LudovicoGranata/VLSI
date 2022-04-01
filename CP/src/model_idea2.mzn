include "globals.mzn";
include "gecode.mzn";
int: n_circuits;   % Number of circuits
set of int: CIRCUITS = 1..n_circuits;  

int: width;   % fixed width of the grid
set of int: WIDTH = 0..width; 
array[CIRCUITS, 1..2] of int: circuit_dimensions; %width and height of the circuits
array[CIRCUITS] of int: circuit_dimension_x = [circuit_dimensions[c,1]|c in CIRCUITS];
array[CIRCUITS] of int: circuit_dimension_y = [circuit_dimensions[c,2]|c in CIRCUITS];
array[CIRCUITS] of int: areas = [circuit_dimension_x[c] * circuit_dimension_y[c] | c in CIRCUITS];
int: max_height = sum ([circuit_dimensions[c, 2] | c in CIRCUITS]);
array [CIRCUITS] of var 0..width-min([circuit_dimensions[c,1]|c in CIRCUITS]) : solution_x;
array [CIRCUITS] of var 0..max_height-min([circuit_dimensions[c,2]|c in CIRCUITS]) : solution_y;
var int: height = max(c in CIRCUITS)(solution_y[c] + circuit_dimensions[c,2]);


%constraint alldifferent( [solution_y[t]*width + solution_x[t] | t in CIRCUITS])::domain;
constraint diffn (solution_x,solution_y,circuit_dimension_x, circuit_dimension_y)::domain; 
constraint forall (c in CIRCUITS) (solution_x[c] + circuit_dimension_x[c] <= width)::domain;
constraint forall (c in CIRCUITS)(solution_y[c] + circuit_dimension_y[c] <= height)::domain;
constraint forall (c in CIRCUITS) (solution_x[c] < width)::domain;
constraint forall (c in CIRCUITS)(solution_y[c]  < height)::domain;
%constraint max ( [solution[c,1]+ circuit_dimensions[c,1] | c in CIRCUITS])<=width;
%constraint max ( [solution[c,2]+ circuit_dimensions[c,2] | c in CIRCUITS])<=height;

constraint cumulative(solution_y, circuit_dimension_y, circuit_dimension_x, width)::domain;
constraint cumulative(solution_x, circuit_dimension_x, circuit_dimension_y, height)::domain;


%symmetry constrain breaking
%%if there are two consecutive pieces that have the same width (or heigh) I can swap them freely, to break the simmetry I have to say that always the smaller i will have the smaller position.

%constraint symmetry_breaking_constraint (forall (i,j in CIRCUITS where i<j) (( solution_x[i]==solution_x[j] /\ circuit_dimension_x[i]==circuit_dimension_x[j] ) -> solution_y[i] <= solution_y[j]));
%constraint symmetry_breaking_constraint (forall (i,j in CIRCUITS where i<j) (( solution_y[i]==solution_y[j] /\ circuit_dimension_x[i]==circuit_dimension_y[j] ) -> solution_x[i] <= solution_x[j]));

%constraint symmetry_breaking_constraint (forall (i,j in CIRCUITS where i<j) ((circuit_dimension_x[i]==circuit_dimension_x[j] /\  circuit_dimension_y[i]==circuit_dimension_y[j] ) -> solution[i,1] <= solution[j,1]));


%constraint symmetry_breaking_constraint ( lex_lesseq ( solution_x, [width - 1 -solution_x[c]-circuit_dimension_x[c]| c in CIRCUITS] ) );
%constraint symmetry_breaking_constraint ( lex_lesseq ( solution_y, [height- 1 -solution_y[c]-circuit_dimension_y[c]| c in CIRCUITS] ) );

ann:search_ann_x;
ann:search_ann_y;
%search_ann = int_search(solution, input_order, indomain_min);
%search_ann = int_search(solution, first_fail, indomain_min);
%search_ann = int_search(solution, dom_w_deg, indomain_min); 
%search_ann = int_search(solution, input_order, indomain_random);
search_ann_x = int_search(solution_x, dom_w_deg, indomain_random); 
search_ann_y = int_search(solution_y, dom_w_deg, indomain_random);


solve ::search_ann_x
      ::search_ann_y
      :: restart_luby(250)
  minimize height;


output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions[c,1])++ " " ++ show(circuit_dimensions[c,2])++ " " ++ show(solution_x[c]) ++ " "++ show(solution_y[c])|
c in CIRCUITS ]









