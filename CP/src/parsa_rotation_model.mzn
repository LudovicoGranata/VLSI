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

set of int: HOR_DIM_R_DOM = min_dim..min([max_dim, width]);
set of int: VER_DIM_R_DOM = min_dim..max_dim;

array[CIRCUITS] of var HOR_DIM_R_DOM: hor_dim_r;
array[CIRCUITS] of var VER_DIM_R_DOM: ver_dim_r;
array[CIRCUITS] of var bool: rotated;


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

constraint diffn(circuitx, circuity, hor_dim_r, ver_dim_r)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + hor_dim_r[i]) <= width )
/\	( (circuity[i] + ver_dim_r[i]) <= height)
);

constraint exists(i in CIRCUITS) ( circuitx[i] == 0 /\ circuity[i] == 0 );

constraint cumulative(circuitx, hor_dim_r, ver_dim_r, height)::domain;
constraint cumulative(circuity, ver_dim_r, hor_dim_r, width)::domain;

constraint forall(i in CIRCUITS) ( 
	(rotated[i] -> (hor_dim_r[i] == ver_dim[i] /\ ver_dim_r[i] == hor_dim[i])) /\ (not (rotated[i]) -> (ver_dim_r[i] == ver_dim[i] /\ hor_dim_r[i] == hor_dim[i]))
);


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - ver_dim_r[i])
/\	(circuitx_sym[i] == width - circuitx[i] - hor_dim_r[i])
);

constraint lex_greatereq(circuitx, circuitx_sym);
% constraint lex_greatereq(circuity, circuity_sym); removes solutions?


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve :: seq_search([
		int_search(circuity, dom_w_deg, indomain_min),
		bool_search(rotated, dom_w_deg, indomain_random),
		int_search(circuitx, dom_w_deg, indomain_random) ])
	minimize height;

output ["height=\(height)\n",
		"circuitx=\(circuitx)\n",
		"circuity=\(circuity)\n",
		"hor_dim=\(hor_dim_r)\n",
		"ver_dim=\(ver_dim_r)\n"]