include "globals.mzn";
include "gecode.mzn";
int: n_circuits;   % Number of circuits
set of int: CIRCUITS = 1..n_circuits;  

int: width;   % fixed width of the grid
set of int: WIDTH = 0..(width-1); 
array[CIRCUITS, 1..2] of int: circuit_dimensions; %width and height of the circuits -- change the name to circuit_dimensions
array[CIRCUITS] of int: CIRCUITS_ORDERED = sort_by(CIRCUITS, [-circuit_dimensions[c,1]*circuit_dimensions[c,2] | c in CIRCUITS]);
array[CIRCUITS] of int: circuit_dimensions_ordered_x = [circuit_dimensions[CIRCUITS_ORDERED[c],1] | c in CIRCUITS];
array[CIRCUITS] of int: circuit_dimensions_ordered_y =[circuit_dimensions[CIRCUITS_ORDERED[c],2] | c in CIRCUITS];
int: max_height = sum ([circuit_dimensions_ordered_y[c] | c in CIRCUITS]);
int: min_height = (sum([circuit_dimensions_ordered_x[c] * circuit_dimensions_ordered_y[c] | c in CIRCUITS]) div width);
array[CIRCUITS,1..2] of var int: solution;
array[CIRCUITS] of var 0..width: solution_x;
array[CIRCUITS] of var 0..max_height: solution_y; 
constraint(solution_x==col(solution,1));
constraint(solution_y==col(solution,2));

var min_height..max_height: height = max(c in CIRCUITS)(solution_y[c] + circuit_dimensions_ordered_y[c]);

%main constraints
constraint forall (c in CIRCUITS) (solution_x[c]< width)::domain;
constraint forall (c in CIRCUITS)(solution_y[c] < height)::domain;
constraint diffn (solution_x, solution_y, circuit_dimensions_ordered_x, circuit_dimensions_ordered_y); 
constraint forall (c in CIRCUITS) (solution_x[c]+ circuit_dimensions_ordered_x[c] <= width)::domain;
constraint forall (c in CIRCUITS)(solution_y[c] + circuit_dimensions_ordered_y[c] <= height)::domain;

%implied constraint
constraint cumulative(solution_y, circuit_dimensions_ordered_y, circuit_dimensions_ordered_x, width);
constraint cumulative(solution_x, circuit_dimensions_ordered_x, circuit_dimensions_ordered_y,  height);

%symmetry constrain breaking
array[CIRCUITS,1..2] of var int: solution_sym_x;
array[CIRCUITS,1..2] of var int: solution_sym_y;
array[CIRCUITS,1..2] of var int: solution_sym_xy;

constraint forall(c in CIRCUITS)(solution_sym_x[c,1]=(width)-solution_x[c]-circuit_dimensions_ordered_x[c] /\ solution_sym_x[c,2]=solution_y[c]);
constraint forall(c in CIRCUITS)(solution_sym_y[c,2]=(height)-solution_y[c]-circuit_dimensions_ordered_y[c] /\ solution_sym_y[c,1]=solution_x[c]);
constraint forall(c in CIRCUITS)(solution_sym_xy[c,1]=(width)-solution_x[c]-circuit_dimensions_ordered_x[c] /\ solution_sym_xy[c,2]=(height)-solution_y[c]-circuit_dimensions_ordered_y[c]);

constraint symmetry_breaking_constraint ( lex_less ( array1d(solution), array1d(solution_sym_x)) /\ lex_less ( array1d(solution), array1d(solution_sym_y)) /\ lex_less ( array1d(solution), array1d(solution_sym_xy)));

%symmetry breaking constraint per due blocchi in verticale e orizzontale
constraint symmetry_breaking_constraint (forall(c,k in CIRCUITS where c!=k)( ((solution_x[c]==solution_x[k] /\ circuit_dimensions_ordered_x[c]==circuit_dimensions_ordered_x[k] /\ solution_y[c]+circuit_dimensions_ordered_y[c]==solution_y[k]) -> c<k ) /\  ((solution_x[c]==solution_x[k] /\ circuit_dimensions_ordered_x[c]==circuit_dimensions_ordered_x[k] /\ solution_y[c]+circuit_dimensions_ordered_y[c]==solution_y[k]) -> c<k )));

%constraint symmetry_breaking_constraint (forall(c,k in CIRCUITS where c!=k)( if (solution_x[c]==solution_x[k] /\ circuit_dimensions_ordered_x[c]==circuit_dimensions_ordered_x[k] /\ solution_y[c]+circuit_dimensions_ordered_y[c]==solution_y[k]) then c<k endif /\ if (solution_x[c]==solution_x[k] /\ circuit_dimensions_ordered_x[c]==circuit_dimensions_ordered_x[k] /\ solution_y[c]+circuit_dimensions_ordered_y[c]==solution_y[k]) then c<k  endif));

%symmetry breaking constraint per due blocchi in orizzontale
%constraint symmetry_breaking_constraint (forall(c,k in CIRCUITS where c!=k)( (solution_y[c]==solution_y[k] /\ circuit_dimensions_ordered_y[c]==circuit_dimensions_ordered_y[k] /\ solution_x[c]+circuit_dimensions_ordered_x[c]==solution_x[k]) -> c<k  ));

%per due blocchi uguali che possono essere swappati

%constraint symmetry_breaking_constraint(  solution_x[1] == 0 /\ solution_y[1] == 0);%the biggest block has to be in the bottom left corner


ann:search_ann;
%search_ann = int_search(solution, input_order, indomain_min);
%search_ann = int_search(solution, first_fail, indomain_min);
%search_ann = int_search(solution, dom_w_deg, indomain_min); 
%search_ann = int_search(solution, input_order, indomain_random);
search_ann = int_search(solution, dom_w_deg, indomain_random); 


solve ::search_ann
      :: restart_luby(150)
      ::relax_and_reconstruct(array1d(solution), 40) 
  minimize height;


output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions_ordered_x[c])++ " " ++ show(circuit_dimensions_ordered_y[c])++ " " ++ show(solution[c,1]) ++ " "++ show(solution[c,2])|
c in CIRCUITS ];

output ["\n" ++ show(solution_sym_x)];

%problem with 30,32,35,37,38,39,40





