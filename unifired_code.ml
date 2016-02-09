(* All Code unified in one file 
for easy compile and debug *)

(* Exact real datatype *)
datatype 'a seq = Cons of 'a * (unit -> 'a seq);
datatype exreal = R of int * int seq;
datatype Sierpinski = Sierp of bool seq;
datatype 'a opens = cfo of ('a -> Sierpinski);
datatype 'a closed = cfc of ('a -> Sierpinski);
datatype 'a cptset = cpt of (('a opens) opens);
datatype prefix_real = pref_r of int * int list;
datatype Interval = I of exreal * exreal;



fun head (Cons(x,_)) = x;
fun tail (Cons(_,xf)) =xf();

fun zeros () = Cons(0,fn ()=>zeros ());
fun ones () = Cons(1,fn ()=>ones ());
fun mones () = Cons(~1,fn ()=>mones ());



(* Conversion between real and exact real *)
fun ll2r _ 0 _ = 0.0
|	ll2r (Cons(x,xq)) n i = (Real.fromInt(x)/(Math.pow(2.0,i))) + (ll2r (xq()) (n-1) (i+1.0));

fun exr2r (R(i,f)) n = Real.fromInt(i)+(ll2r f n 1.0);

fun r2ll x 0 i = zeros()
| 	r2ll x n i = if Real.signBit(x - 1.0/Math.pow(2.0,i)) then Cons(0,fn ()=> r2ll x (n-1) (i+1.0))
				else Cons(1, fn ()=> r2ll (x- 1.0/Math.pow(2.0,i)) (n-1) (i+1.0)); 

fun r2exr r n = (R(floor r, r2ll (r - Real.fromInt(floor r)) (n) (1.0)));







(* Addition *)
fun take (0, xq) = []
  | take (n, Cons(x,xf)) = x :: take (n-1, xf());


fun nlength [] = 0
  | nlength (x::xs) = 1 + nlength xs;

fun frac2list_1 (0, xq) = []
  | frac2list_1 (n, Cons(x,xf)) = x :: frac2list_1 (n-1, xf());

fun frac2list x = frac2list_1(~1,x); 


fun eval_result x = if (take(2,x) =[1,2] orelse take(2,x)=[~1,~2]) then Cons(0, fn()=>eval_result(Cons(0,fn ()=>tail(tail(x))))) 
					else if (take(3,x)=[1,1,1] orelse take(3,x)=[1,1,2]) then eval_result(Cons(0, fn()=>Cons(~1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[~1,~1,~1] orelse take(3,x)=[~1,~1,~2]) then eval_result(Cons(0, fn()=>Cons(1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[1,1,0] orelse (take(3,x)=[1,1,~1] orelse take(3,x)=[1,1,~2])) then Cons(1, fn()=>eval_result(Cons(1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[~1,~1,0] orelse (take(3,x)=[~1,~1,1] orelse take(3,x)=[~1,~1,2])) then Cons(~1, fn()=>eval_result(Cons(~1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[1,~1,~1] orelse take(3,x)=[1,~1,~2]) then Cons(0, fn()=>eval_result(Cons(1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[1,~1,0] orelse (take(3,x)=[1,~1,1] orelse take(3,x)=[1,~1,2])) then Cons(1, fn()=>eval_result (Cons(~1,fn ()=>tail(tail(x)))))
					else if take(2,x) = [1,~2] then Cons(0, fn()=>eval_result (Cons(0,fn ()=>tail(tail(x)))))
					else if take(2,x) = [1,0] then Cons(1, fn()=>eval_result (Cons(0,fn ()=>tail(tail(x)))))
					else if take(2,x) = [0,2] then Cons(1, fn()=>eval_result(Cons(0,fn ()=>tail(tail(x)))))
					else if take(2,x) = [0,~2] then Cons(~1, fn()=>eval_result(Cons(0,fn ()=>tail(tail(x)))))
					else if take(2,x) = [0,0] then Cons(0, fn()=>eval_result(Cons(0,fn ()=>tail(tail(x)))))
					else if (take(3,x) = [0,1,2] orelse take(3,x)=[0,1,1]) then Cons(1, fn()=>eval_result(Cons(~1,fn ()=>tail(tail(x)))))
					else if (take(3,x) = [0,1,~2] orelse (take(3,x)=[0,1,~1] orelse take(3,x)=[0,1,0])) then Cons(0, fn()=>eval_result(Cons(1,fn ()=>tail(tail(x)))))
					else if (take(3,x) = [0,~1,~2] orelse take(3,x)=[0,~1,~1]) then Cons(~1, fn()=>eval_result(Cons(1,fn ()=>tail(tail(x)))))
					else if (take(3,x) = [0,~1,2] orelse (take(3,x)=[0,~1,1] orelse take(3,x)=[0,~1,0])) then Cons(0, fn()=>eval_result(Cons(~1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[~1,1,1] orelse take(3,x)=[~1,1,2]) then Cons(0, fn()=>eval_result(Cons(~1,fn ()=>tail(tail(x)))))
					else if (take(3,x)=[~1,1,0] orelse (take(3,x)=[~1,1,~1] orelse take(3,x)=[~1,1,~2])) then Cons(0, fn()=>eval_result (Cons(~1,fn ()=>tail(tail(x)))))
					else if take(2,x) = [~1,0] then Cons(~1, fn()=>eval_result (Cons(0,fn ()=>tail(tail(x)))))
					else if take(2,x) = [~1,2] then Cons(0, fn()=>eval_result (Cons(0,fn ()=>tail(tail(x))))) else eval_result(Cons(0,fn()=>tail(x)));      


fun first_var (x,y) = x;
fun sec_var (x,y) = y;
fun frac_sum1 (Cons(x,xq),Cons(y,yq)) = Cons(x+y,fn ()=>(frac_sum1(xq(),yq())));
fun rplus (R(x1,y1)) (R(x2,y2)) = let val temp = frac_sum1(y1,y2) in 
										if head(temp) = 2 orelse (take(2,temp)=[1,2] orelse (take(3,temp)=[1,1,1] orelse take(3,temp)=[1,1,2])) then (R(x1+x2+1,eval_result (temp)))
										else if head(temp) = ~2 orelse (take(2,temp)=[~1,~2] orelse (take(3,temp)=[~1,~1,~1] orelse take(3,temp)=[~1,~1,~2])) then (R(x1+x2-1,eval_result (temp)))
										else (R(x1+x2,eval_result(temp)))
									end; 

fun multplus ([x]) = x
|	multplus (x::xs) = rplus (x) (multplus xs); 






fun frac_sum x y = let val temp = frac_sum1(x,y) in 
										if head(temp) = 2 orelse (take(2,temp)=[1,2] orelse (take(3,temp)=[1,1,1] orelse take(3,temp)=[1,1,2])) then (1,eval_result (temp))
										else if head(temp) = ~2 orelse (take(2,temp)=[~1,~2] orelse (take(3,temp)=[~1,~1,~1] orelse take(3,temp)=[~1,~1,~2])) then (~1,eval_result (temp))
										else (0,eval_result(temp))
									end;


fun list_frac_plus ([x]) = x
|	list_frac_plus (x::xs) = sec_var( frac_sum (x) (list_frac_plus xs));






(* multiplication *)
(* the fraction multiply with fraction is curently slow and cause the slow of multiplication *)

fun revApp ([], ys) = ys
| revApp (x::xs, ys) = revApp (xs, x::ys);

fun tobinary n = let
  fun tb' 0   acc = acc
    | tb' num acc = tb' (num div 2) (num mod 2 :: acc)
in
  tb' n []
end;

fun todecimal1 [] acc = 0
|	todecimal1 (x::xs) acc = x*acc + (todecimal1 xs acc*2);

fun todecimal x = todecimal1 (revApp (x,[])) 1;


fun split ([], _) = (0,[0])
|	split ([x], a) = (x,a)
|	split ((x::xs), y) = split(xs, y@[x]);


fun minus_f (Cons(x,xf)) = Cons(~1*x, fn ()=> (minus_f (xf())));

fun r_minus (R(i,f)) = (R(~1*i,(minus_f (f))));

fun get 1 x =head(x)
|	get k x = get (k-1) (tail(x));


fun addz 0 x 0 = zeros()
|	addz 0 x 1 = x
|	addz 0 x (~1) = minus_f(x)
|	addz n x z = Cons(0,fn ()=> addz (n-1) x z);

fun addele x (Cons(0,yq)) n = Cons((addz n x 0), fn ()=> (addele x (yq()) (n+1))) 
|	addele x (Cons(1,yq)) n = Cons((addz n x 1), fn ()=> (addele x (yq()) (n+1))) 
|	addele x (Cons(~1,yq)) n = Cons((addz n x ~1), fn ()=> (addele x (yq()) (n+1)));


fun mult_frac_aux1 k x =
	let val temp = list_frac_plus(take(3,x)) in 
		(get k temp, Cons(temp,fn()=> tail(tail(tail(x)))))
	end;


fun mult_frac_aux2 x k = 
	let val temp = mult_frac_aux1 k x in
		Cons(first_var(temp), fn ()=> (mult_frac_aux2 (sec_var(temp)) (k+1)))
	end;

fun mult_frac x y = mult_frac_aux2 (addele x y 1) 1;

fun tailn 0 x = x
|	tailn n x = tailn (n-1) (tail(x));

fun list_exr ([]) (y) (n) (res) = res
|	list_exr (1::x) y n res = list_exr x y (n+1) ((R(todecimal(take(n,y)),(tailn n y)))::res)
|	list_exr (0::x) y n res = list_exr x y (n+1) res;   


fun mult_frac_int x y = let val temp = revApp(tobinary x,[]) in
									multplus (list_exr temp y 0 [])
						end;

fun rmult (R(i1,f1)) (R(i2,f2)) = rplus (R(i1*i2, mult_frac (f1) (f2))) (rplus (mult_frac_int i1 (f2)) (mult_frac_int i2 (f1)));






(* Sierpinski Space *)


fun c_true () = Cons(true, fn ()=>c_true());
fun c_false () = Cons(false, fn ()=>c_false());




fun sierp_extract_seq (Sierp(x)) = x;

fun interleave (Cons(x,xf), yq) = Cons(x, fn()=> interleave(yq, xf()));

fun sierp_or (Sierp(a)) (Sierp(b)) = Sierp(interleave(a,b));

fun sierp_and (Sierp(Cons(x,xf))) (Sierp(Cons(y,yf))) = 
	if x=true then (Sierp(Cons(y,yf)))
	else (Sierp(Cons(false,fn ()=> sierp_extract_seq (sierp_and (Sierp(Cons(y,yf))) (Sierp(xf()))))));


fun sierp_and_ls [] = (Sierp(c_true()))
|	sierp_and_ls (s::ss) = (Sierp(Cons(false, fn ()=> (sierp_extract_seq(sierp_and s ((sierp_and_ls ss)))))));



fun sierp_is_top (Sierp(Cons(x,xq))) = 
	if x = true 
	then true 
	else sierp_is_top (Sierp(xq()));

fun append ([],ys) = ys
	| append (x::xs,ys) = x::append(xs,ys);

fun multi_sierp_or (Cons((Sierp(Cons(x,xq))),sf)) = 
	if x = true
	then (Sierp(c_true()))
	else (Sierp(Cons(false, fn()=>interleave (sierp_extract_seq(multi_sierp_or (sf())),(xq())) )));

fun list_sierp_or ((Sierp(Cons(x,xq)))::xs) = Sierp(Cons(x,fn ()=> (sierp_extract_seq(list_sierp_or (xs@[(Sierp(xq()))])))))
|	list_sierp_or [] = Sierp(c_false());




(* Open Set and Closed Set *)


fun opens_union (cfo(x)) (cfo(y)) = cfo (fn a => (sierp_or (x a) (y a))); 

fun opens_intersection (cfo(x)) (cfo(y)) = (cfo(fn a => sierp_and (x a) (y a)));



(* Hausdoff *)
fun check1m1 (Cons(x,xq),Cons(y,yq)) = 
	if x=1 
	then if y= ~1 
		then Cons(false, fn ()=> check1m1(xq(),yq()))
		else c_true()
	else c_true();

fun check0m1 (Cons(x,xq),Cons(y,yq)) = 
	if x=0 
	then if y= ~1 
		then Cons(false, fn ()=> check0m1(xq(),yq()))
		else c_true()
	else c_true();


fun checkm1m1 (Cons(x,xq),Cons(y,yq)) = 
	if x= ~1 
	then if y= ~1 
		then Cons(false, fn ()=> checkm1m1(xq(),yq()))
		else c_true()
	else c_true();


fun check10 (Cons(x,xq),Cons(y,yq)) = 
	if x=1 
	then if y=0 
		then Cons(false, fn ()=> check10(xq(),yq()))
		else c_true()
	else c_true();
fun check00 (Cons(x,xq),Cons(y,yq)) = 
	if x=0 
	then if y=0 
		then Cons(false, fn ()=> check00(xq(),yq()))
		else c_true()
	else c_true();
fun checkm10 (Cons(x,xq),Cons(y,yq)) = 
	if x= ~1 
	then if y=0 
		then Cons(false, fn ()=> check10(xq(),yq()))
		else c_true()
	else c_true();

fun check11 (Cons(x,xq),Cons(y,yq)) = 
	if x=1 
	then if y= 1 
		then Cons(false, fn ()=> check11(xq(),yq()))
		else c_true()
	else c_true();

fun check01 (Cons(x,xq),Cons(y,yq)) = 
	if x=0 
	then if y= 1 
		then Cons(false, fn ()=> check01(xq(),yq()))
		else c_true()
	else c_true();

fun checkm11 (Cons(x,xq),Cons(y,yq)) = 
	if x= ~1 
	then if y= 1 
		then Cons (false, fn ()=>checkm11(xq(),yq()))
		else c_true()
	else c_true();


fun notEqual_seq (Cons(x,xq)) (Cons(y,yq)) = 
	if x-y = 1 then Cons(false, fn ()=> notEqual_seq (xq()) (Cons(head(yq())-2, fn ()=> tail(yq()) ))) 
	else if y-x = 1 then Cons(false, fn ()=> notEqual_seq (yq()) (Cons(head(xq())-2, fn ()=> tail(xq()) )))
	else if x=y then Cons(false, fn ()=> notEqual_seq (xq()) (yq()))
	else if x-y=2 then checkm11(xq(),yq())
	else if y-x=2 then check1m1(xq(),yq())
	else c_true();


fun notEqual (R(ix,fx)) (R(iy,fy)) = 
	if ix = iy then Sierp(notEqual_seq (fx) (fy))
	else if ix-iy=2 then Sierp(checkm11(fx,fy))
	else if iy-ix=2 then Sierp(check1m1(fx,fy))
	else if ix-iy=1 then Sierp(notEqual_seq (fx) (Cons(head(fy)-2, fn ()=> tail(fy))))
	else if iy-ix=1 then Sierp(notEqual_seq (fy) (Cons(head(fx)-2, fn ()=> tail(fx))))
	else Sierp(c_true());

fun checkm1 (Cons(x,xq)) = Cons(not(x=(~1)), fn ()=> checkm1 (xq()));

fun check1 (Cons(x,xq)) = Cons(not(x=1), fn ()=> check1 (xq()));


fun isPositive (R(0,Cons(x,xq))) = 
	if x=0 then 
		(Sierp(Cons(false,fn ()=> (sierp_extract_seq (isPositive (R(0,xq()))))))) 
	else
		if x=1 then 
			(Sierp(checkm1 (Cons(x,xq)))) 
		else (Sierp(check1 (Cons(x,xq))))
|	isPositive (R(1,f)) = (Sierp(checkm1 (f)))
|	isPositive (R(i,f)) = 
	if i>1 then 
		(*mones*)
		(Sierp(c_true()))
	else (Sierp(c_false()));






(*Admisibility*)




fun makeinterval (I(l,r)) = cfo(fn z => 
								(let val a = (isPositive ((rplus (z) (r_minus(l))))) in
									let val b = (isPositive ((rplus (r) (r_minus(z))))) in
										(sierp_and (a) (b))
									end
								end)
							);

fun get(0,xq) = []
| 	get(n,Cons(x,xf)) = x :: get(n-1,xf());


fun exr2pref (R(i,f)) n = pref_r(i,get(n,f));

fun list2lazym1 [] = mones()
|	list2lazym1 (x::xs) = Cons(x, fn()=>(list2lazym1 xs) );

fun list2lazy1 [] = ones()
|	list2lazy1 (x::xs) = Cons(x, fn()=>(list2lazy1 xs) );

fun pref2exrm1 (pref_r(i,f)) = (R(i,(list2lazym1 f)));
fun pref2exr1 (pref_r(i,f)) = (R(i,(list2lazy1 f)));

fun make_pref_interval x = makeinterval (I((pref2exrm1 x),(pref2exr1 x)));

(*map interval *)
fun table(n) = Cons(makeinterval( I((R(n-1,zeros())),(R(n+1,zeros())))), fn ()=> table(n+1));

fun mapq f (Cons(x,xq)) = (Cons(f x, fn ()=> (mapq f (xq()))));

(*find index for interger part*)
fun map f [] = [] 
|	map f (x::xs) = (f x) :: (map f xs);

fun take_head (Sierp(Cons(x,xf))) = x;

fun checktrue [] n = ~1
|	checktrue (x::xs) n = if x=true then n else checktrue xs (n+1);

fun index_list x = checktrue (map take_head x) 0;

(* cl stands for current list, ll stands for current list length, ci stands for current index, which is what we wanted. *)
fun findindex_i (Cons(Sierp(Cons(x,xf)), sf)) cl ci = 
	if x=true then ci else
		if index_list cl = ~1 then 
		findindex_i (sf()) (cl@[Sierp(xf())]) (ci+1)
		else index_list cl; 

fun findindex_f (Sierp(Cons(x,xf))) (Sierp(Cons(y,yf))) (Sierp(Cons(z,zf)))
	= if x=true then 1 else if y=true then 0 else if z=true then ~1 else findindex_f (Sierp(xf())) (Sierp(yf())) (Sierp(zf()));

fun admisibility_aux x (pref_r(i,f)) = 
	let 
	val temp = (findindex_f (x (make_pref_interval((pref_r(i,f@[1]))))) (x (make_pref_interval((pref_r(i,f@[0]))))) (x (make_pref_interval((pref_r(i,f@[~1]))))))
	in
		Cons(temp, fn ()=> (admisibility_aux x (pref_r(i,f@[temp]))))
	end;





(* help testing,

fun singleton x = (cpt(cfo (fn u=> ((getf u) x))));


fun admisibility1 (cpt(cfo(x))) = (R(0, (admisibility_aux (x) (pref_r(0,[])))));

fun testcase (cpt(cfo(x))) = x (make_pref_interval((pref_r(0,[1]))));

*)



(* Compact Set *)


fun sierp_c (Sierp(Cons(true,xq))) = (Sierp(Cons(false,fn ()=>sierp_extract_seq (sierp_c(Sierp(xq()))))))
|	sierp_c (Sierp(Cons(false,xq))) = (Sierp(Cons(true,fn ()=>sierp_extract_seq (sierp_c(Sierp(xq()))))));

fun complementc (cfc(x)) = (cfo(x));

fun complemento (cfo(x)) = (cfc(x));

fun cfc_intsec_cpt (f) (cpt(cfo(x : (('a opens)->Sierpinski)))) = (cpt(cfo(fn a => (x (opens_union (complementc(f)) a)))));

exception Do_not_Look;

fun handle_aux x = if head(sierp_extract_seq x)=true then (Sierp(c_true()))
					else ((Sierp(Cons(false,fn ()=> (sierp_extract_seq((handle_aux (Sierp(tail(sierp_extract_seq(x)))))) handle Do_not_Look => (c_false())))     )) );

fun auxf f = (fn x => (f x handle Do_not_Look=> (Sierp(c_false()))));

fun multiappend [] = []
|	multiappend (x::xs) = x@(multiappend xs);

fun disguise_aux (x::xs) = Cons(x,fn ()=> disguise_aux xs)
|	disguise_aux [] = raise Do_not_Look;

fun disguise (pref_r(x,xs)) = (R(x,(disguise_aux(xs))));

fun generate_dis (pref_r(x,xs)) = [disguise(pref_r(x,xs@[1])), disguise(pref_r(x,xs@[0])), disguise(pref_r(x,xs@[~1]))];
fun generate_pref (pref_r(x,xs)) = [(pref_r(x,xs@[1])),(pref_r(x,xs@[0])),(pref_r(x,xs@[~1]))];

fun dis_seq (x) = Cons((map disguise (x)) , fn ()=> dis_seq (multiappend (map generate_pref (x))));

val pr = dis_seq([(pref_r(0,[0])),(pref_r(0,[1])),(pref_r(0,[~1]))]);

(*fun aux_f f = (fn x =>(handle_aux (f x)));*)

fun compact_aux f x = Cons((handle_aux (sierp_and_ls (map (auxf f) (head(x))))), fn () => (compact_aux f (tail(x))));

fun compact f x = multi_sierp_or (compact_aux f x);

fun admisibility (cpt(cfo(x))) = 

	let val temp = (findindex_i (mapq x (table(1))) [] 1) in

		(R(temp, (admisibility_aux (x) (pref_r(temp,[])))))
	end;


fun headls (x::xs) =x;
fun taills [] =[]
|	taills (x::xs) = xs;



fun compact1 f [] _ = (Sierp(c_true()))
|	compact1 f (x::xs) x_result = 
			(if (head(sierp_extract_seq(x_result))) = true
				then if (xs=[]) then (Sierp(c_true())) else (compact1 f xs (f (disguise (headls(xs)))))
			else (Sierp(Cons(false, fn ()=> (sierp_extract_seq(compact1 f xs (Sierp((tail(sierp_extract_seq(x_result))))))))))    )
			handle Do_not_Look => (Sierp(Cons(false, fn ()=> (sierp_extract_seq(compact1 f (xs@(generate_pref x)) (f (disguise (headls(xs@(generate_pref x))))))))));


fun compact_new f = compact1 f [(pref_r(0,[]))] (f (disguise (pref_r(0,[])))); 











fun eval_sierp_aux _ 0 = false 
|	eval_sierp_aux (Cons(true,xq)) n = true
|	eval_sierp_aux (Cons(false,xq)) n = eval_sierp_aux (xq()) (n-1);


fun eval_sierp x n = eval_sierp_aux (sierp_extract_seq(x)) n;

fun getf (cfo(f)) = f;

val unitint = (cpt(cfo(fn f => compact (getf f) pr)));




(*

testing how timer works. *)

val testtimer = 
let val t = Timer.startCPUTimer()
   in
   (testadd 0.14 0.17, Time.toString(#usr(Timer.checkCPUTimer(t))) ^ "second")
end;





(*
	debug
*)

(*
fun getfrac (R(i,f)) n = take(n, f);

fun getff (R(i,f)) = f;
*)

fun testadd	a b =exr2r	(rplus (r2exr a 100) (r2exr b 100)) 100;















