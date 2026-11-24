import YM.MS.Orbit.Bear
/-!
# Dressing, baking for absolute mode. Wave identities exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Rake Flux Cog Wire Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x y z:Lengths G}
  {F H:Law G}{X Y:Rake.Site G I}{S:Planet G I}{P:Latch.Edge G}
local notation "Γ"=> field (parity (C:=G.ColorIndex) ( A:=Axis ))
lemma split_hook (hp:Split x y z): hook lace x*hook lace y=hook lace z:= by simpa [hook] using ( (split_perm hp).map lace ).prod_eq
lemma sleeve_used (i:BH G)(q:QP)(x:Lengths G): sleeve lace F ((i,q)::x)= flag i (-q)*hook lace x*F ((i,q)::x):= rfl
-- (not assuming parity/reality of F). no-Rev? radius simplifies.Stamp.P.
lemma hearth (p:QP)(i j: BH G)(u k f:ℂ): dope P i j p * (flag i (-p)*u)*(flag j p*k*f) = P i j p * ( u*k*f ):= by
   let b:= P i j p; rw [dope_p]; calc
      _ = flag i p*flag i (-p)*(flag j p*flag j (-p))* P i j p * (u*k*f) := by ring
      _ = _:= by rw [flag_,flag_,one_mul,one_mul]
lemma shapeTr (K:Latch.Edge G)(F:Law G)(p:QP)(w:Lengths G): trc (dope K) p ( sleeve lace F ) w=hook lace w * trc K p F w:= by
   simp only [at_trc, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; let T:= F ((i,p)::(j,-p)::w); rw [ sleeve_used ]; rw [ show hook lace ((j,-p)::w)=flag j p*hook lace w from (by change flag j (- -p)* _=_; rw [neg_neg]; rfl) ]; let L:= hook lace w; change dope K i j p * (flag i (-p)*(flag j p*L)*T)=_; calc
       _ = dope K i j p * (flag i (-p)*1)*(flag j p*L*T):= by ring
       _ = _:= by rw [hearth]; unfold L T; ring
lemma skin_c (μ:Measure QP) : cycle (dope P) μ ( sleeve lace F )= sleeve lace ( cycle P μ F ):= by funext w; unfold cycle; simp_rw [shapeTr,integral_const_mul]; rfl
lemma vi_dope (hp:Split x y z)(p:QP)(i j:BH G): viν false ( dope P ) i j ( sleeve lace F ) ( sleeve lace H ) x y p= hook lace z * viν false P i j F H x y p:= by
   unfold viν; rw [ ← split_hook hp, sleeve_used,sleeve_used, show Opp false p= -p from rfl, neg_neg ]; let U:= F ((i,p)::x); let V:= H ((j,-p)::y); let A:= hook lace x; let B:= hook lace y; let c:ℂ:= cross (parity j) (degree Γ x); calc
      _ = 2*c * ( dope P i j p * ( flag i (-p)*A )*( flag j p * B * V ) ) * U:= by unfold A B U V c; ring
      _ = _:= by rw [hearth]; unfold A B U V c; ring
lemma D_tree (h:Reverse P parity): tree parity (dope P) ( sleeve lace F ) (sleeve lace H)= sleeve lace ( tree parity P F H ):= by
   funext w; unfold tree; let T:= allocate Γ w ( R:=ℂ); change T _= hook lace w • T _; rw [← map_smul]; refine scatter_congr _ _ _ _ (fun l r hp=>?_ ); simp only [Pi.smul_apply, convertR h,convertR (Dk_rev h), smul_eq_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_; exact vi_dope hp (-net l) i j
lemma Dcrew (A:Cover)(μ:Measure QP): PairV false μ A A (dope P) ( sleeve lace F ) (sleeve lace H)= sleeve lace (PairV false μ A A P F H):= by
    funext x; let T:= allocate Γ x (R:=ℂ); change T _= hook lace x • T _; rw [ ← map_smul ]; refine scatter_congr _ _ _ _ (fun l r he=>?_); change be A _ * _=hook lace x*(be A _ * _); rw [mul_left_comm]; simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; simp_rw [ vi_dope he, mul_left_comm (be A _) (hook lace x), integral_const_mul ]; ring
end YM.MS.Orbit
