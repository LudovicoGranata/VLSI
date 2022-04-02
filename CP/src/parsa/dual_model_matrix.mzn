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
% ==================== DUAL MODEL ====================
% ====================================================

% => this model is slow !!!

set of int: MATRIX_WIDTH = 0..width-1;
set of int: MATRIX_HEIGHT = 0..max_height-1;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix;

% ============= Channeling Constraints ===============
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx[k]<=i /\ circuitx[k]+hor_dim[k]>i /\ circuity[k]<=j /\ circuity[k]+ver_dim[k]>j) <-> (matrix[j,i] == k));


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - ver_dim[i])
/\	(circuitx_sym[i] == width - circuitx[i] - hor_dim[i])
);

array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_X_symmetry;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_Y_symmetry;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_XY_symmetry;

constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx_sym[k]<=i /\ circuitx_sym[k]+hor_dim[k]>i /\ circuity[k]<=j /\ circuity[k]+ver_dim[k]>j) <-> (matrix_X_symmetry[j,i] == k));
	
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx[k]<=i /\ circuitx[k]+hor_dim[k]>i /\ circuity_sym[k]<=j /\ circuity_sym[k]+ver_dim[k]>j) <-> (matrix_Y_symmetry[j,i] == k));
	
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx_sym[k]<=i /\ circuitx_sym[k]+hor_dim[k]>i /\ circuity_sym[k]<=j /\ circuity_sym[k]+ver_dim[k]>j) <-> (matrix_XY_symmetry[j,i] == k));

constraint lex_greatereq(array1d(matrix), array1d(matrix_X_symmetry));
constraint lex_greatereq(array1d(matrix), array1d(matrix_Y_symmetry));
constraint lex_greatereq(array1d(matrix), array1d(matrix_XY_symmetry));

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