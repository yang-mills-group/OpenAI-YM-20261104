import YM.SchemeRG11.Outer.Pave
/-! Assemble one mark scaled at n and its G,W
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew MvPolynomial
open scoped Classical Pointwise
variable {I:Type}{G:Gauge} (s:Finset I) (p:I→ pLabel G) {n m:ℕ}{T: Align.Itinerary}
local notation "D₁"=> Atoll.land G
variable [DecidableEq I](t:Landmarks I)
lemma emission(t:I → Cover)(h:ℝ)(v:pLabel G)(o:I)(ho:o∈s) : coverGod s (update p o v) h t= (D₁).avg (cross (t o) (castZero h v) * aerial (s.erase o) (fun l=>castZero h (p l)) t):=by
 apply congrArg (D₁).avg; unfold aerial; rw [← Finset.mul_prod_erase _ _ ho]; simp only [Function.update_self]; apply congrArg; exact Finset.prod_congr rfl (fun j hj=>by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
lemma area(o:I)(ho:o∈s)(h:IsWeightedHomogeneous generation (p o) n)(R:ℝ)(B:Window)(i:ℕ):
 let a:=T.gap i
 let p0:=castZero 1 (p o)
 let Q:=aerial (s.erase o) (fun l=>castZero a (p l)) (fun l=>motionP t o l i)
 let W:= North.escort (cove T B i) (gateY T R i)
 (∑ j:Axis,∑ k:Axis,nearTag s p B t T o j k R i)= a^(-(n:ℤ))*(D₁).avg (W * p0*Q) :=by
 intro a p0 Q W
 have he : castZero (T.gap i) (p o)=a^(-(n:ℤ)) • p0:=by rw [castFree,plume_s _ h,_root_.map_smul]; unfold p0; rw [castFree]
 simp_rw [nearTag, placement s p _ _ ho,he,mul_smul_comm,smul_mul_assoc,map_smul]
 unfold W North.escort; simp_rw [Finset.sum_mul,map_sum]; -- RHS smul
 conv_rhs=> simp only [smul_mul_assoc,map_smul]
 simp only [Finset.sum_mul,map_sum, smul_eq_mul, Finset.mul_sum]; rw [Finset.sum_comm (s:=gateY T R i)]
 -- order (k,j,x) to x,j,k
 apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro x _; exact mul_left_comm ..
lemma evaporation(o:I)(h:IsWeightedHomogeneous generation (p o) n)(R:ℝ)(B:Window)(i:ℕ) :
 let f:=motionP t o; let u:=T.gap i; let W:=North.escort (cove T B i) (gateY T R i); let q:=stemZero 1 (p o); let Q:= aerial (s.erase o) (fun l=>castZero u (p l)) (fun l=> f l i)
 (∑ j:Axis,∑ k:Axis,u^4*∑ x∈gateY T R i,cove T B i x*inside0 (s.erase o) f p (p o) T j k i x) = u^(-(n:ℤ))*(D₁).avg ((D₁).neg.heat (W*q)*Q):=by
 intro f u W q Q
 unfold inside0 W North.escort; simp only [plume_s n h (T.gap i),mul_smul_comm,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,Finset.mul_sum,smul_eq_mul]
 rw [Finset.sum_comm (s:=gateY T R i)]; apply Finset.sum_congr rfl; intro j _;rw [Finset.sum_comm];apply Finset.sum_congr rfl; intro k _;apply Finset.sum_congr rfl; intro x _; unfold q Q u; have he:= T.positive i; field_simp

structure Dab (u:ℕ)(F: Frames G) where
 m:ℕ
 A:Fin m→ Tab F u
 M:ℕ→ Fin m→ℝ
variable {F: Frames G}
variable (T)
def Dab.tile (d:Dab n F)(q: pLabel G)(R:ℝ)(B:Window)(i:ℕ):vellum G:= T.gap i^(-(n:ℤ)) • (crestF q T B R i-∑j,d.M i j • stemZero 1 (d.A j).p)
abbrev waveS (u:ℝ)(a n:ℕ):=u^(-(n:ℤ)+(a:ℤ))
abbrev Dab.rangeV(d:Dab n F)(i:ℕ)(j:Fin d.m):=waveS (T.gap i) (d.A j).k n * d.M i j
variable {T}
def markC (o:I)(T: Itinerary)(d:Dab n F)(i:ℕ):ℝ:=
 let a:=T.gap i; let v(l):= t l i
 (D₁).avg (cross (v o) (castFirst a (p o))* aerial (s.erase o) (fun j=>castZero a (p j)) v)-∑ l:Fin d.m,Dab.rangeV T d i l * coverGod s (Function.update p o (d.A l).p) a v
lemma mapC(o:I)(h:IsWeightedHomogeneous generation (p o) n)(ho:o∈s)(i:ℕ)(d:Dab n F):
 let u:=T.gap i
 let Q:= aerial (s.erase o) (fun k=> castZero u (p k)) (fun k=>motionP t o k i)
 markC s p t o T d i= u^(-(n:ℤ))*(D₁).avg ((castFirst 1 (p o)-(D₁).neg.heat (∑j,d.M i j • stemZero 1 (d.A j).p))*Q):=by
 intro u Q; dsimp only [markC]
 rw [switch s p o (fun j=>t j i), (dominion _ _ h).2, smul_mul_assoc,_root_.map_smul]; simp only [emission s p _ _ _ _ ho,switch s p o (fun j=>t j i),sub_mul,map_sub, map_sum,map_smul,mul_sub,Finset.sum_mul]
 rw [zpow_neg,zpow_natCast,Finset.mul_sum]; congr 1
 · rw [inv_pow];rfl
 apply Finset.sum_congr rfl; intro j _; rw [(dominion _ _ (d.A j).hom).1, castFree,smul_mul_assoc,map_smul]; unfold Dab.rangeV waveS; simp only [smul_eq_mul, smul_mul_assoc,_root_.map_smul]; let a:=d.A j; rw [zpow_add₀ (T.positive i).ne',zpow_neg,zpow_natCast,zpow_natCast]
 unfold Q motionP u; rw [inv_pow]; have he:=T.positive i; field_simp -- check
end YM.SchemeRG11.Dock
