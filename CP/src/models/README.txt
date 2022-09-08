DO NOT DELETE OR MODIFY THIS FILE !!!

Models
base_v1: x,y s.b. constraint + two_stack + three_stack
base_v2: largest circuit on 0,0 + two_stack + three_stack

In the models with "largest circuit on 0,0",
I added that in the stacking constraints we will not consider the block on 0,0
=> This avoids deleting some valid solutions

Test da fare:
- Find best searching strategy
	- Best restart (constant, linear, geomertic, luby, none)
	- Best variable choice annotation (input_order, first_fail, smallest, dom_w_deg)
	- Best variable value selection (min, median, random, split)
	- With or without relax_and_reconstruct
- Find best model
	- with xy sb constraint
	- OR largest block on 0,0

How to find best searching strategy?
- Use 5 instances
- Use complete model with all the constraints
1. Find best variable choice annotation (restart=luby(100); selection=random) => dom_w_deg
2. Find best value selection (restart=luby(100)) => indomain_random
3. Find best restart option => restart_luby
4. Relax_and_reconstruct => with

How to find best model?
- Use all instances
- Use best searching strategy

Dual model?
- Write about it but say it was discarded

1.
input_order: 5/5, avg=10064
first_fail: 5/5, avg=11253
smallest: 4/5, avg=25087
=> dom_w_deg: 5/5, avg=1228

2.
min:  5/5, 2001
median 3/5, 1076
=> random 5/5 1188
split 5/5 1235

3.
=> restart_luby 5/5 1133
restart_geometric 5/5 1163
restart_linear 5/5 25376
restart_constant 4/5 34407

4.
=> With 5/5 1465
without 5/5 1603