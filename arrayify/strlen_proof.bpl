procedure main(v0 : int, length0 : int, a0_input : [int]int) 
returns (a0 : [int]int, retval : int)
requires (v0 == 0); // Initial index of pointer is 0
requires (length0 > 0); // Length of the array must be positive
requires (exists i:int :: 0 <= i && i < length0 && a0_input[i] == 0); // Array is null-terminated
{
var v9 : int;
var v7 : int;
var v4 : int;
var v3 : int;
var v12 : int;
var v11 : int;
var v10 : int;
var v.0 : int;
a0 := a0_input;
codelabel0_0:
codelabel0_phi2_1:
v.0 := v0;
assert (0 <= v.0);
assert !((length0 <= v.0));
v3 := a0[v.0];
if (!((v3 == 0))) {
v4 := 1;
} else {
v4 := 0;
}
if ((v4 == 0)) {
codelabel0_8:
v9 := v.0;
v10 := v0;
v11 := (v9 + -1 * v10);
v12 := v11;
retval := v12;

} else if ((v4 == 1)) {
codelabel0_5:
codelabel0_6:
v7 := (v.0 + 1);
codelabel0_phi2_2:
// Restating the inductive invariants of this loop for Boogie
assert (v7 >= 0);
assert (v7 < length0);
// Either the current character is null or there exists a null character later in the array
assert (a0[v7] == 0 || (exists i:int :: (v7 < i && i < length0 && a0[i] == 0)));
v.0 := v7;
assert (0 <= v.0);
assert !((length0 <= v.0));
v3 := a0[v.0];
if (!((v3 == 0))) {
v4 := 1;
} else {
v4 := 0;
}
if ((v4 == 0)) {
codelabel1_8:
v9 := v.0;
v10 := v0;
v11 := (v9 + -1 * v10);
v12 := v11;
retval := v12;

} else if ((v4 == 1)) {
// Since v4 == 1, we know that a0[v7] != 0, and so there exists a null character later in the array
// This implies that v7 is not the last character, and so v7 + 1 is a valid index
assert (v7 + 1 < length0);
codelabel1_5:
codelabel1_6:
v7 := (v.0 + 1);
goto codelabel0_phi2_2;


}


}

}
