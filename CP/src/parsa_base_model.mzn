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

int: max_height = round((sum(i in CIRCUITS)(ver_dim[i]))/2);
int: min_height = max(i in CIRCUITS)(ver_dim[i]);
set of int: HEIGHT_DOM = min_height..max_height;
var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width-min(i in CIRCUITS)(hor_dim[i]);
set of int: CIRCUITY_DOM = 0..max_height-min(i in CIRCUITS)(ver_dim[i]);
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

constraint diffn(circuitx, circuity, hor_dim, ver_dim)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + hor_dim[i]) <= width )
/\	( (circuity[i] + ver_dim[i]) <= height)
);

constraint exists(i in CIRCUITS) ( circuitx[i] == 0 /\ circuity[i] == 0 );

constraint cumulative(circuitx, hor_dim, ver_dim, height)::domain;
constraint cumulative(circuity, ver_dim, hor_dim, width)::domain;


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - ver_dim[i])
/\	(circuitx_sym[i] == width - circuitx[i] - hor_dim[i])
);

constraint lex_greatereq(circuitx, circuitx_sym);
% constraint lex_greatereq(circuity, circuity_sym); removes solutions?


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve :: seq_search([
		int_search(circuity, dom_w_deg, indomain_min),
		int_search(circuitx, dom_w_deg, indomain_random) ])
	minimize height;

output ["height=\(height)\n",
		"circuitx=\(circuitx)\n",
		"circuity=\(circuity)\n",
		"hor_dim=\(hor_dim)\n",
		"ver_dim=\(ver_dim)\n"]