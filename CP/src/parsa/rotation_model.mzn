include "globals.mzn";

% ====================================================
% ================ PROBLEM PARAMETERS ================
% ====================================================

int: width;
int: n_circuits;

set of int: CIRCUITS = 1..n_circuits;
array[CIRCUITS, 1..2] of int: circuit_dimensions;

% ============= Conversion to my model ===============
array[CIRCUITS] of int: hor_dim = [circuit_dimensions[i,1] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim = [circuit_dimensions[i,2] | i in CIRCUITS];


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = round((sum(i in CIRCUITS)( max([hor_dim[i], ver_dim[i]]) ) )/2);
int: min_height = min(i in CIRCUITS)(max([hor_dim[i], ver_dim[i]]));
set of int: HEIGHT_DOM = min_height..max_height;
var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width-min(i in CIRCUITS)(min([hor_dim[i], ver_dim[i]]));
set of int: CIRCUITY_DOM = 0..max_height-min(i in CIRCUITS)(min([hor_dim[i], ver_dim[i]]));
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;

int: max_dim = max(hor_dim ++ ver_dim);
int: min_dim = min(hor_dim ++ ver_dim);

set of int: DIM_1_DOM = min_dim..min([max_dim, width]);
set of int: DIM_2_DOM = min_dim..max_dim;

array[CIRCUITS] of var DIM_1_DOM: dim_1;
array[CIRCUITS] of var DIM_2_DOM: dim_2;
array[CIRCUITS] of var bool: rotated;

array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS,
	[- hor_dim[i]*ver_dim[i] | i in CIRCUITS] );
array[CIRCUITS] of int: hor_dim_ord = [hor_dim[circuits_ordered[i]] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim_ord = [ver_dim[circuits_ordered[i]] | i in CIRCUITS];


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

constraint diffn(circuitx, circuity, dim_1, dim_2)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + dim_1[i]) <= width )
/\	( (circuity[i] + dim_2[i]) <= height)
);

constraint cumulative(circuitx, dim_1, dim_2, height)::domain;
constraint cumulative(circuity, dim_2, dim_1, width)::domain;

constraint forall(i in CIRCUITS) ( 
	(rotated[i] -> (dim_1[i] == ver_dim_ord[i] /\ dim_2[i] == hor_dim_ord[i])) /\ (not (rotated[i]) -> (dim_2[i] == ver_dim_ord[i] /\ dim_1[i] == hor_dim_ord[i]))
);

% constraint forall(i in CIRCUITS) ((dim_1[i] == dim_2[i]) -> rotated[i] = false);

% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - dim_2[i])
/\	(circuitx_sym[i] == width - circuitx[i] - dim_1[i])
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
		(dim_2[i] == dim_2[j] /\ dim_1[i] == dim_1[j]) -> (
			( (circuitx[i] == circuitx[j]) -> (circuity[i] < circuity[j]) )
		/\ 	( (circuity[i] == circuity[j]) -> (circuitx[i] < circuitx[j]) )
		)
	)
);


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: int_search(circuity, input_order, indomain_min)
	:: bool_search(rotated, dom_w_deg, indomain_random)
	:: int_search(circuitx, input_order, indomain_random)
	minimize height;

output ["height=\(height)\n",
		"circuitx=\(circuitx)\n",
		"circuity=\(circuity)\n",
		"hor_dim=\(dim_1)\n",
		"ver_dim=\(dim_2)\n",
		"rotated=\(rotated)\n"]