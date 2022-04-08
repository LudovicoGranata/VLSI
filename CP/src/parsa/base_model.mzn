include "globals.mzn";
include "gecode.mzn";

% ====================================================
% ================ PROBLEM PARAMETERS ================
% ====================================================

int: width;
int: n_circuits;

set of int: CIRCUITS = 1..n_circuits;
array[CIRCUITS, 1..2] of int: circuit_dimensions;

% ============= Conversion to my model ===============
array[CIRCUITS] of int: hor_dim = col(circuit_dimensions, 1);
array[CIRCUITS] of int: ver_dim = col(circuit_dimensions, 2);


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = sum(ver_dim);
int: min_height = max(ver_dim);
set of int: HEIGHT_DOM = min_height..max_height;

var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width - min(hor_dim);
set of int: CIRCUITY_DOM = 0..max_height - min(ver_dim);
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;

% ================= Ordered circuit ==================
array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS,
	[ -(hor_dim[i]*ver_dim[i]) | i in CIRCUITS] );
array[CIRCUITS] of int: hor_dim_ord = [hor_dim[circuits_ordered[i]] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim_ord = [ver_dim[circuits_ordered[i]] | i in CIRCUITS];


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

constraint diffn(circuitx, circuity, hor_dim_ord, ver_dim_ord)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + hor_dim_ord[i]) <= width )
/\	( (circuity[i] + ver_dim_ord[i]) <= height)
);


% ================ Implied constraints ===============
constraint cumulative(circuitx, hor_dim_ord, ver_dim_ord, height)::domain;
constraint cumulative(circuity, ver_dim_ord, hor_dim_ord, width)::domain;


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - ver_dim_ord[i])
/\	(circuitx_sym[i] == width - circuitx[i] - hor_dim_ord[i])
);

% ============= Largest circuit on (0,0) =============
% int: largest_circuit_index = arg_max([hor_dim_ord[i]*ver_dim_ord[i] | i in CIRCUITS]);
% constraint (circuitx[largest_circuit_index] == 0) /\ (circuity[largest_circuit_index] == 0);

% ============== S.B. on x and y axis ================
constraint symmetry_breaking_constraint (
	lex_lesseq(circuitx, circuitx_sym)
);
constraint symmetry_breaking_constraint (
	lex_lesseq(circuity, circuity_sym)
);

% => Seems better to keep xy symmetries than larger circuit on (0,0)

% =========== S.B. on 2 stacking circuits ============

predicate two_stack_ver(int: i, int: j) = (
	((circuitx[i] == circuitx[j]) /\ hor_dim_ord[i] == hor_dim_ord[j] /\ ver_dim_ord[i] + ver_dim_ord[j] == max([circuity[i]+ver_dim_ord[i],circuity[j]+ver_dim_ord[j]]) - min([circuity[i],circuity[j]])) -> circuity[i] < circuity[j]
);

predicate two_stack_hor(int: i, int: j) = (
	((circuity[i] == circuity[j]) /\ ver_dim_ord[i] == ver_dim_ord[j] /\ hor_dim_ord[i] + hor_dim_ord[j] == max([circuitx[i]+hor_dim_ord[i],circuitx[j]+hor_dim_ord[j]]) - min([circuitx[i],circuitx[j]])) -> circuitx[i] < circuitx[j]
);

constraint symmetry_breaking_constraint (
	forall (i,j in CIRCUITS where i<j) (two_stack_ver(i,j) /\ two_stack_hor(i,j))
);

% constraint symmetry_breaking_constraint (
% 	forall (i,j in CIRCUITS where i<j) (two_stack_hor(i,j))
% );

% ============ S.B. on 3 circuit blocks ==============
% constraint symmetry_breaking_constraint (
% 	forall (i,j,k in CIRCUITS where i!=j /\ j!=k /\ i!=k)(
% 		( (circuity[i] == circuity[j]) /\ ver_dim_ord[i] == ver_dim_ord[j] /\ hor_dim_ord[i] + hor_dim_ord[j] == max([circuitx[i]+hor_dim_ord[i],circuitx[j]+hor_dim_ord[j]]) - min([circuitx[i],circuitx[j]]) /\ circuitx[k] == min( [circuitx[i],circuitx[j]]) /\ hor_dim_ord[k] == hor_dim_ord[i] + hor_dim_ord[j] /\ ver_dim_ord[k] + ver_dim_ord[i] == max([circuity[k]+ver_dim_ord[k],circuity[i]+ver_dim_ord[i]]) - min([circuity[k],circuity[i]]))
% 			-> circuity[k] < circuity[i]
% 	)
% );

% constraint symmetry_breaking_constraint (
% 	forall (i,j,k in CIRCUITS where i!=j /\ j!=k /\ i!=k)(
% 		(((circuitx[i] == circuitx[j]) /\ hor_dim_ord[i] == hor_dim_ord[j] /\ ver_dim_ord[i] + ver_dim_ord[j] == max([circuity[i]+ver_dim_ord[i],circuity[j]+ver_dim_ord[j]]) - min([circuity[i],circuity[j]])) /\ circuity[k] == min([circuity[i], circuity[j]]) /\ ver_dim_ord[k] == ver_dim_ord[i] + ver_dim_ord[j] /\ hor_dim_ord[k] + hor_dim_ord[i] == max([circuitx[k]+hor_dim_ord[k],circuitx[i]+hor_dim_ord[i]]) - min([circuitx[k],circuitx[i]]))
% 		-> circuitx[k] < circuitx[i]
% 	)
% );


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: seq_search( [
		int_search(circuity, input_order, indomain_min),
		int_search(circuitx, input_order, indomain_min) ] )
	:: restart_luby(150)
	minimize height;


output [ 
	show(width) ++ " " ++ show(height) ++ " \n" ++ 
	show(n_circuits) ] ++[ "\n" ++ 
	show(hor_dim_ord[c])++ " " ++ show(ver_dim_ord[c])++ " " ++ 
	show(circuitx[c]) ++ " "++ show(circuity[c])
	| c in CIRCUITS ]