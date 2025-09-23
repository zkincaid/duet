procedure main(v0 : int, lengtha0 : int, a0_input : [int]int) 
returns (a0 : [int]int, retval : int)
{
var v9 : int;
var v7 : int;
var v4 : int;
var v3 : int;
var v12 : int;
var v11 : int;
var v10 : int;
var v_0 : int;
a0 := a0_input;
codelabel0_0:
codelabel0_phi2_1:
v_0 := v0;
assert (0 <= v_0);
assert !((lengtha0 <= v_0));
v3 := a0[v_0];
if (!((v3 == 0))) {
v4 := 1;
} else {
v4 := 0;
}
if ((v4 == 0)) {
codelabel0_8:
v9 := v_0;
v10 := v0;
v11 := (v9 + -1 * v10);
v12 := v11;
retval := v12;

} else if ((v4 == 1)) {
codelabel0_5:
codelabel0_6:
v7 := (v_0 + 1);
codelabel0_phi2_2:
v_0 := v7;
assert (0 <= v_0);
assert !((lengtha0 <= v_0));
v3 := a0[v_0];
if (!((v3 == 0))) {
v4 := 1;
} else {
v4 := 0;
}
if ((v4 == 0)) {
codelabel1_8:
v9 := v_0;
v10 := v0;
v11 := (v9 + -1 * v10);
v12 := v11;
retval := v12;

} else if ((v4 == 1)) {
codelabel1_5:
codelabel1_6:
v7 := (v_0 + 1);
goto codelabel0_phi2_2;


}


}

}
