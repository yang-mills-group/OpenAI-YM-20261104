import YM.Comparison.RG02.Assembly.Radial
import YM.Comparison.RG02.Cumulants.Partition
import YM.Comparison.RG02.Order.Vacancy
/-! The whole marked jet as a two-headed series, with the quiet denominator *before* taking logarithmic marginals. This is coefficient arithmetic alone and applies to unmasked input kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.CommonCover.JetCumulants
open Finset PowerSeries Function Marker Multi Comparison Comparison.RG02 Order Order.Join Extra.Trajectories Cumulants
open scoped BigOperators Classical
variable {I:Type}[DecidableEq I][Fintype I](R:Census I)
variable {A A':Type*}[CommRing A][CommRing A'][Algebra ℂ A][Algebra ℂ A']
abbrev Table (R:Census I)(A:Type*):= R.Mode → A
local notation "Tp" t:max=> Table R t
abbrev basis1 {A:Type*}[One A][Zero A](k:R.Mode):A:= if k=R.quiet then 1 else 0
noncomputable def mixDatum {A:Type*}[Mul A][AddCommMonoid A](x y:Tp A)(z:R.Mode):A:=∑ t:R.Mode,∑ v:R.Mode,if Poly.merges t v z then x t*y v else 0
noncomputable def chamberPow {A:Type*}[One A][Mul A][AddCommMonoid A] (x:Tp A):ℕ→Tp A
   | 0 =>basis1 R
   | n+1=>mixDatum R (chamberPow x n) x
lemma curve_change (π:A→ₐ[ℂ]A') (n:ℕ) (x:Tp A) : π ∘ chamberPow R x n=chamberPow R (π ∘ x) n := by
  induction n with
  | zero => funext i; change π (if _ then _ else _)= _; rw [chamberPow]; unfold basis1; split_ifs <;> simp_all
  | succ n h=>
     funext i; change π (mixDatum _ _ _ i)=mixDatum _ _ _ i; simp_rw [mixDatum,map_sum,← h]; exact sum_congr rfl fun k _=> sum_congr rfl fun j _=> by split_ifs <;> simp
local notation "PS"=> PowerSeries
local notation "PolyA"=>Poly R
noncomputable def depot (x:Tp (PS ℂ)) : PTable R:=PowerSeries.mk (fun n=>Poly.inject fun t=>coeff n (x t))
noncomputable def ship (x:PS ℂ): PTable R:=PowerSeries.map (Poly.bead R) x
lemma depot_known (x:Tp (PS ℂ))(a b): (coeff a (depot R x)).part b=coeff a (x b):=by rw [depot,coeff_mk]; rfl
lemma depot_one : depot R (basis1 R)=1:= by
   ext1 i; ext t; rw [coeff_one]; rw [depot_known]; unfold basis1; split_ifs <;> simp_all [Poly.one_part,basis1]
lemma depot_zero : depot R (0:Tp (PS ℂ))=0 := by ext1 i; ext t; rw [map_zero,Poly.part_nil]; rw [depot_known]; simp only [Pi.zero_apply,map_zero]
lemma depot_neg (x:Tp (PS ℂ)): depot R (-x) = - depot R x := by ext1 i; ext t; rw [map_neg,Poly.part_neg]; rw [depot_known,depot_known,Pi.neg_apply,map_neg]
lemma depot_add (x y:Tp (PS ℂ)): depot R (x+y)= depot R x+depot R y:= by ext1 i; ext t; rw [map_add,Poly.part_plus]; simp_rw [depot_known,Pi.add_apply,map_add]
variable {J:Type*}
lemma depot_sum {s:Finset J}(x:J→Tp (PS ℂ)): depot R (∑ i∈s,x i)=∑ i∈s,depot R (x i) := by
    classical induction s using Finset.induction with | empty=> rw [sum_empty,sum_empty,depot_zero] | insert i s he hi=>rw [sum_insert he,sum_insert he,depot_add,hi]
lemma depot_mul (y x:Tp (PS ℂ)): depot R (mixDatum R y x)=depot R y * depot R x := by
    ext1 i; ext t; rw [depot_known,coeff_mul,Poly.part_sum,mixDatum,map_sum]; simp_rw [Poly.part_mul,depot_known,map_sum]; rw [sum_comm (s:=antidiagonal i)]; simp_rw [sum_comm (s:=antidiagonal i)] -- verify
    refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_; split_ifs <;> simp [coeff_mul, *]
lemma depot_scale (f:Tp (PS ℂ))(x:PS ℂ) : depot R (fun a=>x*f a)=ship R x *depot R f:= by
    ext1 i; ext t; rw [depot_known,coeff_mul,coeff_mul,Poly.part_sum,ship]; apply sum_congr rfl; intro a ha; rw [PowerSeries.coeff_map, show (Poly.bead R) (coeff a.1 x)*(coeff a.2 _) = (coeff a.1 x) • (coeff a.2 (depot R f)) from (Algebra.smul_def (coeff a.1 x) (_:Poly R)|>.symm),Poly.part_smul,depot_known]
lemma depot_pow (f:Tp (PS ℂ))(n:ℕ):depot R (chamberPow R f n)=depot R f ^ n:= by induction n with | zero=> rw [pow_zero, chamberPow,depot_one] | succ n hi=>rw [pow_succ,chamberPow,depot_mul,hi]
lemma sold_scalar (x:ℂ)(y:PTable R) : ship R (PowerSeries.C x)*y=x • y:=Algebra.smul_def x y |>.symm
noncomputable def expTable (x:Tp A)(t:R.Mode):A:=∑ i∈range (Fintype.card I+1), (i.factorial : ℂ)⁻¹ • chamberPow R x i t
noncomputable def logTable (x:Tp A)(t:R.Mode):A:=∑ i∈range (Fintype.card I+1), (-↑(i+1:ℕ):ℂ)⁻¹ • chamberPow R (basis1 R-x) (i+1) t
abbrev letter (A':I→A)(t:R.Mode):A:=∑ i:I,if t=R.fire i then (A' i:A) else 0
lemma depot_positive (x:Tp (PS ℂ)): depot R (expTable R x)=Assembly.markExp (depot R x):= by
    rw [show expTable R x=∑ i∈range (Fintype.card I+1), fun t=>(i.factorial:ℂ)⁻¹ • chamberPow R x i t from by funext i; unfold expTable; rw [Finset.sum_apply],depot_sum]; apply Finset.sum_congr rfl; intro j hj; rw [← sold_scalar,←depot_pow,←depot_scale]
    congr 1; funext k; rw [Algebra.smul_def]; rfl
variable {R}
lemma table_transfer (π:A→ₐ[ℂ]A') (y:Tp A)(t:R.Mode): π (expTable R y t)=expTable R (π∘y) t ∧ π (logTable R y t)=logTable R (π∘y) t := by
    have h:π ∘ ((basis1 R)-y)=basis1 R-π∘y:=by
         funext z; change π (basis1 R z - y z)= _; rw [map_sub]; unfold basis1; split_ifs <;> simp [*]
    constructor
    · change π (∑ i∈range _,_)=_; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=> congr_arg _ ?_; exact congr_fun (curve_change R π i y) t
    change π (∑ i∈range _,_)=_; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _; apply congr_arg _; exact congr_fun ((curve_change R π _ _).trans (congr_arg (fun w=>chamberPow R w (i+1)) h)) t
variable (R)
lemma concrete (x:PolyA)(n:ℕ)(t:R.Mode): chamberPow R x.part n t=(x^n).part t:=by
    induction n generalizing t with
    | zero=>rw [pow_zero,Poly.one_part]; rfl
    | succ n hi=> rw [pow_succ,Poly.part_mul]; apply sum_congr rfl fun k _=>sum_congr rfl fun j _=>?_; split_ifs; rw [hi]; rfl
lemma exhibits (x:PolyA)(t:R.Mode): expTable R x.part t=x.pass.part t ∧ ((x.part R.quiet)=1→logTable R x.part t=(Extra.Trajectories.connected x).part t):=by
   let h:=concrete R x; unfold expTable
   constructor
   · simp_rw [h,smul_eq_mul, Poly.pass,Poly.part_sum,Poly.part_smul]
   intro hp; have hh:basis1 R-x.part=(1-x).part:=by funext i; rw [Extra.Trajectories.part_sub,Poly.one_part]; rfl
   simp only [logTable,Cumulants.log_formula hp,Cumulants.unipotentLog,hh]; rw [Poly.part_sum]; apply sum_congr rfl; intro j hj; rw [smul_eq_mul,concrete,Poly.part_smul]; congr 1; exact neg_inv.symm -- type?
lemma exp_letters (u:I→A)(t:R.Mode):expTable R (letter R u) t=∏ j∈t.val,u j:=by
   let V:= MvPolynomial I ℂ; let x(i:I):V:=MvPolynomial.X i; let eval:=MvPolynomial.aeval (R:=ℂ) u; let lhs(i):=letter R x i
   have he : expTable R lhs t=∏ j∈t.val,x j:=by
     apply MvPolynomial.funext; intro w; rw [← MvPolynomial.aeval_eq_eval]; let π:=MvPolynomial.aeval (R:=ℂ) w
     have h:π∘lhs=(Multi.lambda R w).part := by
         funext i; change π (∑ j,_)=(Multi.lambda R w).part i; rw [map_sum,lambda,Poly.part_sum]; refine sum_congr rfl fun v _=>?_ ; split_ifs with hz <;> simp [π,x,Poly.part_send, *] -- split_ifs no visible if on RHS
     change π (expTable _ _ _)=π _; rw [(table_transfer π lhs t).1,h,map_prod,(exhibits R _ t).1,Cumulants.pass_lambda]; simp [π,x]
   have h:eval ∘ lhs= letter R u := by funext k; change eval (∑ i,_)=∑ i,_; refine (map_sum ..).trans (sum_congr rfl fun i _=>by split_ifs <;> simp [eval,x])
   exact (h ▸ (table_transfer eval lhs t).1).symm.trans ((congr_arg eval he).trans (by simp [eval,x]))
lemma mass_log (x:Tp A)(t:R.Mode)(h:x R.quiet=1): logTable R x t= ∑ j∈shards R t,Cumulants.mobiusTop j.val.card • (∏ i∈j.val,x i.val):= by
   let V:= MvPolynomial R.Mode ℂ; let y:R.Mode→V:=fun i=>if i=R.quiet then 1 else MvPolynomial.X i
   let eval(t:R.Mode→ℂ):= MvPolynomial.aeval (R:=ℂ) t; let run(w:Tp A):=MvPolynomial.aeval (R:=ℂ) w
   have hi : logTable R y t=∑ j∈shards R t,Cumulants.mobiusTop j.val.card • (∏ i∈j.val,y i.val):=by
       apply MvPolynomial.funext; intro j; rw [← MvPolynomial.aeval_eq_eval]; change eval j _ = eval j _; rw [(table_transfer _ ..).2,map_sum]; let d:=Poly.inject (eval j ∘ y)
       have hd:eval j∘y=d.part:=rfl; have h_d:d.part R.quiet=1:=by unfold d y; change eval j _=_; simp_all
       rw [show eval j ∘ y=d.part from hd, (exhibits R d t).2 h_d,Cumulants.log_partition d h_d t, ← hd]
       simp_rw [map_smul,map_prod,Function.comp_def]; rfl
   have hg:x=(run x ∘ y):=funext fun i=>by unfold y run; change _=MvPolynomial.aeval x _; dsimp only; split_ifs <;> simp_all
   calc
      logTable R x t = run x (logTable R y t) := by rw [←show (logTable R (run x ∘ y) t)=_ from congr_fun (congr_arg (logTable R) hg.symm) t]; exact (table_transfer _ _ _).2.symm
      _ = _:= by rw [hi,map_sum]; simp_rw [map_smul,map_prod,congr_fun hg,Function.comp_apply]
private lemma mark_power {r:ℕ} {P : Order.Grade R r} (h : Order.bottom R r P=0) (n : ℕ) (s : R.Mode) (t : Order.Index r) (hs : s.val.card < n) :
    (P^n).part (Join.pair s t)=0 := by
  induction n generalizing s t with
  | zero => omega
  | succ n ih=>
    rw [pow_succ,Join.pair_product]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    split
    next hm=>
       by_cases h₀ : k.val.Nonempty
       · have hp : s.val.card=i.val.card + k.val.card := by rw [← hm.1.2,card_union_of_disjoint hm.1.1]
         rw [ih i j (by have hh:= Finset.card_pos.mpr h₀; omega),zero_mul]
       replace h₀ := of_not_not (mt (hot_iff_ne k).2 h₀)
       have he : P.part (Join.pair k l)=0 := by subst k; rw [← show _ = P.part (Join.pair R.quiet l) from (bottom_value P R.quiet l).trans (if_pos rfl),h,Poly.part_nil]
       rw [he,mul_zero]
    next=> rfl
variable {R}
lemma depot_connected (x:Tp (PS ℂ))(h:x R.quiet = 1)(r:ℕ): connected (Order.series R r (depot R x)) = series R r (depot R (logTable R x)) := by
    let v:=depot R x; have he:basis1 R-x=basis1 R+(-x):= sub_eq_add_neg ..
    have hw:1-Order.series R r v=Order.series R r (depot R (basis1 R-x)):= by rw [he,depot_add,depot_one,depot_neg,map_add,map_neg,_root_.map_one,sub_eq_add_neg]
    have hq:(Order.series R r v).part (Board R r).quiet=1:= by rw [← Join.pair_quiet,Order.polarization]; change ( (0:ℕ).factorial : ℂ)* (coeff 0 (depot R x)).part _=_; rw [depot_known,h]; simp
    change connected (Order.series R r v)= _; rw [Cumulants.log_formula hq,Cumulants.unipotentLog,hw,show logTable R x=∑ i∈range (Fintype.card I+1),fun t=>(-((↑(i+1: ℕ)):ℂ))⁻¹ • chamberPow R (basis1 R-x) (i+1) t from by unfold logTable; ext1 k; rw [Finset.sum_apply],depot_sum,map_sum]
    symm; let T:=Order.series R r (depot R (basis1 R-x))
    have ht: bottom R r T = 0 :=by
                                change (bottom R r) ((series R r) _)=0
                                rw [bottom_map]
                                have h':PowerSeries.map (blanked R) (depot R (basis1 R-x))=0:= by
                                                     ext1 i; ext1 t; rw [coeff_map,pure_marks,depot_known];  simp only [Pi.sub_apply,basis1,if_true,h,show 1-(1:PS ℂ)=0 from sub_self _,map_zero,Poly.part_nil,ite_self]
                                rw [h',map_zero]
    calc _ = ∑ n∈range (Fintype.card I+1), (-(↑(n+1:ℕ):ℂ))⁻¹ • T^(n+1):= sum_congr rfl (fun i _=> by
                let a:=( - ((↑(i+1:ℕ)):ℂ))⁻¹
                rw [← map_pow,← depot_pow]; rw [show a • ((series _ r) (depot R (chamberPow R (basis1 R - x) (i+1)))) = (series _ r) (ship R (PowerSeries.C a)*depot R (chamberPow R (basis1 R - x) (i+1))) from ((series_smul ..).symm).trans (congr_arg ((series ..)) ((sold_scalar ..).symm))] -- suspect direction
                -- RHS simply series_smul.symm and congr
                apply congr_arg _; rw [← depot_scale]; apply congr_arg _; funext t; exact Algebra.smul_def ..)
         _= _:= by
               simp_rw [←neg_inv]; exact sum_subset (range_mono (by simp)) (fun i _ hI=> by
                    simp only [mem_range, not_lt] at hI
                    suffices h: T^(i+1)=0 by rw [show (series R r _)^(i+1) = 0 from h,smul_zero]
                    exact Join.both_parts fun j n=> (mark_power _ ht (i+1) j n (lt_of_le_of_lt (Finset.card_le_univ _) (by omega:Fintype.card I < _))).trans (by rw [Poly.part_nil]))
end YM.CommonCover.JetCumulants
