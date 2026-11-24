import YM.Qlocal.Quipu.Brew
import YM.Qlocal.Harmony.Woof
/-!
# Invariant elementary kernel shapes

Use a redundant generating set fixed in each rank, shape-independent (cost after L). Avoid any
possible dimensional dependence on footprint sizes. Keep the very stamps of the estimator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Function Finset Filter Push.AbsoluteSums
open Lattice MeasureTheory Wilson Pressure RG Gauge
open Quipu Quipu.Sonnet
open Marker Stationary
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {V I:Type} [DecidableEq V] {R:Census V} {G:Gauge} {s:Senses R}
    {n r m j k:ℕ} {c:Side}
namespace Shape
noncomputable def varied (A: Vase s G n) (w:↥(paints G n)) : Vase s G n:= {A with ink := w.val, legal:= w.prop}
/-- Check every aspect of the geometry (read-support in the cover, displacement of each marker,
    and choice of represented curvature). -/
structure Form (A B : Vase s G n) : Prop where
    site : A.stage=B.stage
    path : A.maps=B.maps
    read : A.tan=B.tan
namespace Form
variable {A B D: Vase s G n}
protected lemma alike (A: Vase s G n): Form A A:= ⟨rfl,rfl,rfl⟩
protected lemma comm (h:Form A B): Form B A:= ⟨h.site.symm,h.path.symm,h.read.symm⟩
protected lemma step (h:Form A B)(hx:Form B D): Form A D:= ⟨h.site.trans hx.site,h.path.trans hx.path,h.read.trans hx.read⟩
protected lemma ink (h:Form A B)(he:A.ink=B.ink): A=B:= by
 obtain ⟨S,B0,K,L,ha⟩:=A; obtain ⟨S',B1,K',L',he'⟩:=B -- shadow
 obtain ⟨hx,hy,hz⟩:=h; congr
lemma momentum (h:Form A B): A.momentum=B.momentum:= by unfold Vase.momentum Vase.reach; rw [h.path,h.site]
lemma variety (A B: Vase s G n) (a b:↥(paints G n)) (h: Form A B): Form (varied A a) (varied B b):= ⟨h.site,h.path,h.read⟩
end Form
noncomputable def toner (u:Ranks G n): ↥(paints G n):= (paints G n).subtype.leftInverse (fun i=>if u=i then 1 else 0)
noncomputable def pigment (B:↥(paints G n)):= ∑ i:Ranks G n, |B.val i|
lemma pigment_nonneg (B:↥(paints G n)): 0≤pigment B:= by unfold pigment; positivity
lemma tones (A : Vase s G n) (x:Ranks G n): A.ink x= ∑ i:Ranks G n, A.ink i*(toner i).val x:=by
 let P:=paints G n; let a: P:=⟨A.ink,A.legal⟩; let f:= P.subtype.leftInverse
 have hm : a = ∑ i:Ranks G n,A.ink i • toner i:= by
    rw (occs:=.pos [1]) [← LinearMap.leftInverse_apply_of_inj P.ker_subtype a]
    exact LinearMap.pi_apply_eq_sum_univ f _
 change a.val x= _; rw [hm,Submodule.coe_sum, Finset.sum_apply]; rfl
variable (a:ℝ)
noncomputable def legend (i:Ranks G n):= 1+pigment (toner i)
lemma legend_pos (i:Ranks G n) : 0 <legend i:= add_pos_of_pos_of_nonneg zero_lt_one (pigment_nonneg _)
noncomputable def mass (A: Vase s G n)(u:Ranks G n) (a:ℝ):= legend u * Real.exp (a*A.momentum)
lemma mass_filled (A: Vase s G n)(u:Ranks G n): 0 < Shape.mass A u a:= mul_pos (legend_pos _) (Real.exp_pos _)
noncomputable def scales (A: Vase s G n)(u:Ranks G n)(a:ℝ):= varied A ((Shape.mass A u a)⁻¹ • toner u)
local notation "μ"=> (Shape.mass)
noncomputable def tanA (A: Vase s G n)(u:Ranks G n)(a:ℝ):= A.ink u * Shape.mass A u a
local notation "λ'"=> tanA -- context
variable (A: Vase s G n)
lemma same (u:Ranks G n): Form (Shape.scales A u a) A:= ⟨rfl,rfl,rfl⟩
lemma pulse (x:Ranks G n):
    A.ink x= ∑ u:Ranks G n, tanA A u a* (scales A u a).ink x:= by
 rw (occs:=.pos [1]) [tones A x]; refine Finset.sum_congr rfl fun u _=>?_ ; change _= (A.ink u*Shape.mass A u a)*((Shape.mass A u a)⁻¹*(toner u).val x); rw [mul_assoc,mul_inv_cancel_left₀ (mass_filled a A u |>.ne')]; -- check
variable (x:Site c) (U:Config G c) (u:Ranks G n)
lemma imprints : A.read x m U=∑ j:Ranks G n,tanA A j a * (scales A j a).read x m U:=by
 let D(u:Ranks G n):= ∏ j:Fin n,Vase.flavor (k:=m) A (expandAt x U) j (u j) -- namespace
 change ∑ j:Ranks G n,A.ink j*D j=∑ i:Ranks G n,_*∑ j:Ranks G n, (scales A i a).ink j*D j
 rw [show (fun j:Ranks G n=> A.ink j*D j)=(fun j=> (∑ i:Ranks G n,tanA A i a*(scales A i a).ink j)* D j) from funext fun i=> by rw [pulse a A i]]
 simp_rw [Finset.sum_mul,mul_assoc,Finset.mul_sum]; rw [Finset.sum_comm]
lemma freeTicket : (scales A u a).fare a ≤1:=by
 let m:= Shape.mass A u a; let Z:= Real.exp (a*A.momentum); have hm: 0< m:= mass_filled a A u; let F:= scales A u a; change Vase.sizeC F*Z ≤ _; have hu:Vase.sizeC F=m⁻¹*pigment (toner u):= by unfold Vase.sizeC pigment; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; change |m⁻¹* (toner u).val i|=_; rw [abs_mul,abs_of_pos (inv_pos.mpr hm)]
 rw [hu,mul_assoc]; apply le_trans _ (inv_mul_cancel₀ hm.ne' |>.le); apply mul_le_mul_of_nonneg_left; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one); exact Real.exp_nonneg _; exact inv_nonneg.mpr hm.le
lemma price : |tanA A u a| ≤ A.fare a* legend u:= by
 rw [tanA,abs_mul,abs_of_pos (mass_filled a A u)]
 unfold Shape.mass; rw [mul_comm (legend _),← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (legend_pos _|>.le)
 exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun i=> |A.ink i|) (fun i _=> abs_nonneg _) (mem_univ _)) (Real.exp_nonneg _)
lemma spells (B:Vase s G n)(h:Form A B): scales A u a=scales B u a:= by
 have he:Shape.mass A u a=Shape.mass B u a:= by unfold Shape.mass;rw [h.momentum]
 exact (Form.variety A B _ _ h).ink (show (scales A u a).ink=(scales B u a).ink from by unfold scales; rw [he]; rfl)
end Shape
end YM.Qlocal.Harmony
