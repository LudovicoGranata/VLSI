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
array[CIRCUITS] of int: hor_dim = col(circuit_dimensions,1);
array[CIRCUITS] of int: ver_dim = col(circuit_dimensions, 2);


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = round((sum (i in CIRCUITS) (ver_dim[i]))) ;
int: min_height = max(i in CIRCUITS)(ver_dim[i]);
set of int: HEIGHT_DOM = min_height..max_height;

var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width-min(i in CIRCUITS)(hor_dim[i]);
set of int: CIRCUITY_DOM = 0..max_height-min(i in CIRCUITS)(ver_dim[i]);
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;

array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS,
	[- hor_dim[i]*ver_dim[i] | i in CIRCUITS] );
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

% ========= Always have a circuit on (0,0) ===========
constraint exists(i in CIRCUITS) ( circuitx[i] == 0 /\ circuity[i] == 0 );

% ============== S.B. on x and y axis ================
constraint symmetry_breaking_constraint (
	lex_greatereq(circuitx, circuitx_sym)
);
 constraint symmetry_breaking_constraint (
	lex_lesseq(circuity, circuity_sym) % removes solutions ?? => Test
);

% => Useful to add sym breaking on X, Y, XY? Or these two are enough?

% =========== S.B. on identical circuits =============
constraint symmetry_breaking_constraint (
	forall(i,j in CIRCUITS where i<j) (
		(ver_dim_ord[i] == ver_dim_ord[j] /\ hor_dim_ord[i] == hor_dim_ord[j]) -> ((circuity[i] <= circuity[j]) \/
(circuitx[i] <= circuitx[j]) )
		)
	);


constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (circuitx[c]==circuitx[k] /\ hor_dim_ord[c] == hor_dim_ord[k] /\ circuity[c]+ ver_dim_ord[c] = circuity[k]) -> c<k));
constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (circuity[c]==circuity[k] /\ ver_dim_ord[c] == ver_dim_ord[k] /\ circuitx[c]+ hor_dim_ord[c] = circuitx[k]) -> c>k));

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