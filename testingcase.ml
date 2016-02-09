val testtimer = 
let val t = Timer.startCPUTimer()
   in
   (multtest x11 x12 4, Time.toString(#usr(Timer.checkCPUTimer(t))) ^ "second")
end;




val x11 = r2exr 0.237 200;
val x12 = r2exr 0.736 200;
val x11 = r2exr 0.527 200;
val x12 = r2exr 0.859 200;

val x11 = r2exr 0.535 200;
val x12 = r2exr 0.194 200;





val x11 = r2exr 0.527 200;
val x12 = r2exr 0.859 200;
fun getbit 0 f = f
|	getbit n f = getbit (n-1) (tail(f));
fun getfr (R(i,f)) = f; 
fun muleval n x11 x12 = getbit n (getfr (rmult x11 x12));




val x11 = r2ll 0.62 100 1.0;
val x12 = r2ll 0.53 100 1.0;



fun multtest x y n = ll2r (mult_frac x y) n 1.0;