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
int: largest_circuit_index = arg_max([hor_dim_ord[i]*ver_dim_ord[i] | i in CIRCUITS]);
constraint (circuitx[largest_circuit_index] == 0) /\ (circuity[largest_circuit_index] == 0);

% ============== S.B. on x and y axis ================ => incompatible
% constraint symmetry_breaking_constraint (
% 	lex_greatereq(circuitx, circuitx_sym)
% );
% constraint symmetry_breaking_constraint (
% 	lex_lesseq(circuity, circuity_sym)
% );

% ============ S.B. on stacking circuits =============

% Larger circuit, on the bottom
constraint symmetry_breaking_constraint (
	forall (i,j in CIRCUITS where i<j /\ i != largest_circuit_index /\ j != largest_circuit_index) (
		(((circuitx[i] == circuitx[j]) /\ hor_dim_ord[i] == hor_dim_ord[j] /\ ver_dim_ord[i] + ver_dim_ord[j] == max([circuity[i]+ver_dim_ord[i],circuity[j]+ver_dim_ord[j]]) - min([circuity[i],circuity[j]])) -> 
			((ver_dim_ord[i]>=ver_dim_ord[j] -> circuity[i] < circuity[j]) /\ (ver_dim_ord[i]<ver_dim_ord[j] -> circuity[i] > circuity[j])))
	)
);

constraint symmetry_breaking_constraint (
	forall (i,j in CIRCUITS where i<j /\ i != largest_circuit_index /\ j != largest_circuit_index) (
		(((circuity[i] == circuity[j]) /\ ver_dim_ord[i] == ver_dim_ord[j] /\ hor_dim_ord[i] + hor_dim_ord[j] == max([circuitx[i]+hor_dim_ord[i],circuitx[j]+hor_dim_ord[j]]) - min([circuitx[i],circuitx[j]])) -> 
			((hor_dim_ord[i]>=hor_dim_ord[j] -> circuitx[i] < circuitx[j]) /\ (hor_dim_ord[i]<hor_dim_ord[j] -> circuitx[i] > circuitx[j])))
	)
);

% ============ S.B. on 3 circuit blocks ============== => TODO
% constraint symmetry_breaking_constraint (
% 	forall(i,j,k in CIRCUITS where i!=j /\ j!=k /\ i!=k) (
% 		(circuitx[i] == circuitx[j] /\ hor_dim[i] == hor_dim[j] + hor_dim[k] /\ circuitx[j] + hor_dim[j] == circuitx[k] /\ circuity[j] == circuity[k] /\ circuity[i] + ver_dim[i] == circuity[j]) ->
% 			(i<j /\ j<k)
% 	)
% );
% constraint symmetry_breaking_constraint (
% 	forall(i,j,k in CIRCUITS where i!=j /\ j!=k /\ i!=k) (
% 		(circuitx[i] == circuitx[j] /\ hor_dim_ord[i] == hor_dim_ord[j] + hor_dim_ord[k] /\ circuitx[j] + hor_dim_ord[j] == circuitx[k]) ->
% 			(i<j /\ j<k)
% 	)
% );

% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: seq_search( [
		int_search(circuity, input_order, indomain_min),
		int_search(circuitx, input_order, indomain_random) ] )
	:: restart_luby(150)
	minimize height;


		output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(hor_dim_ord[c])++ " " ++ show(ver_dim_ord[c])++ " " ++ show(circuitx[c]) ++ " "++ show(circuity[c])|
c in CIRCUITS ]