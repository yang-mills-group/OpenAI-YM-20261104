import YM.FormalOPE.RG10.GaugeGear.Flight
/-! # Episode rank strict và repeated costs.

 All choices including width relative step-i and canonical comparison (alt orientation)
 at root fed through ROW bounds, not assumed continuation. No production of regime.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open HStein HStein.Tier HStein.Roads Route Route.Bulk MeasureTheory Function Finset PowerSeries
open MvPolynomial (aeval homogeneousComponent totalDegree)
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J X: Type}
local notation "Q"=> Packet (I⊕B)
local notation "L"=> Primitives.GCC.LocalPolynomial.length
local notation "H" => homogeneousComponent

variable (p:Packet I) (n : ℕ)
variable (F:Tier) {u v : I→ℝ}{S:B→ℝ}
lemma covered_h : totalDegree (H n p) ≤ p.totalDegree:= by
 by_cases h : n ≤ p.totalDegree
 · exact (MvPolynomial.homogeneousComponent_isHomogeneous ..).totalDegree_le.trans h
 rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega)]; simp
lemma worth_piece (hu : 0≤u): F.valueOf u (H n p) ≤ F.valueOf u p := by
 rw [F.capital _ hu, F.capital _ hu,MvPolynomial.support_homogeneousComponent];
 apply le_trans (sum_le_sum fun i hi => le_of_eq (show
    F.face u i * ‖MvPolynomial.coeff i (H n p)‖ = F.face u i * ‖MvPolynomial.coeff i p‖ from by rw [MvPolynomial.coeff_homogeneousComponent, if_pos (mem_filter.mp hi).2]))
 exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => mul_nonneg (F.bright _ hu _) (norm_nonneg _))
variable {w : I→Packet B} {C:ℝ}
variable (hu : 0≤ u)(hv:0≤ S)
lemma riseF {j k :ℕ} (hp:totalDegree p≤n+3*j): Guard (PowerSeries.monomial j p) k n:= by
 intro i hi; rw [coeff_monomial]; split_ifs with h; subst i; exact hp; simp
lemma ticket {j k :ℕ}(h:j ≤ k): F.gain u (PowerSeries.monomial j p) k= F.valueOf u p:= by
 rw [F.all_gain,sum_eq_single j]
 · simp
 · intro a _ ha; rw [coeff_monomial, if_neg ha,Tier.zero]
 simp [h]

include hu hv in
lemma straight (p:Packet I) {n:ℕ} (hn : p.IsHomogeneous n) (h0: 0≤C)
 (h : ∀ a,F.valueOf S (w a) ≤ F.value (u a) * C) (h' :∀ a, Tier.free.valueOf S (w a) ≤ C) :
 F.valueOf S (aeval w p) ≤ (2*C)^n * F.valueOf u p:= by
 let W a:= PowerSeries.C (R:=Packet B) (w a)
 have he (b:Letters I): coeff 0 (aeval W (glyph b))= aeval w (glyph b) := by
    suffices he : aeval W (glyph b)= PowerSeries.C (aeval w (glyph b)) by rw [he,coeff_zero_C]
    let C' : Packet B →ₐ[ℂ] Channel B := { __ := PowerSeries.C (R:=Packet B), commutes':=fun c=> by rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]; apply PowerSeries.ext;intro i; cases i <;> simp }
    let R:= C'.comp (aeval (R:=ℂ) w); have hh:R=aeval W:= by ext i : 1; rw [MvPolynomial.aeval_X];change C' (aeval (R:=ℂ) w (MvPolynomial.X i))= _; exact congr_arg C' (MvPolynomial.aeval_X (R:=ℂ) w i)
    rw [← hh]; rfl
 have hw : Targeted F u S W 0 C:= fun i=> by rw [show W i=PowerSeries.C _ from rfl, gain_constant]; exact h i
 have hx : Targeted free u S W 0 C:= fun i=> by rw [show W i=PowerSeries.C _ from rfl,gain_constant,free_stamp,one_mul]; exact h' i
 nth_rw 1 [resolves p]; rw [map_sum,F.capital _ hu,mul_sum]; apply (many F _ hv _ _).trans; apply sum_le_sum; intro i hi
 rw [map_smul,coins,← he]; apply (mul_le_mul_of_nonneg_left ((F.now S hv _ (le_refl 0)).trans (senses hv hu hw hx h0 _)) (norm_nonneg _)).trans; rw [types p _ hn i hi]; exact le_of_eq (by ring)

variable [Fintype J] (M:ℝ)
variable (p' : I→X)(q:B→X)(T:Tape X) {e:Episode I B J} (O:Lens T)
variable (r d:ℕ) [Fintype I] [DecidableEq I]
local notation "A"=> O.m ∘ p'
local notation "Γ"=> O.m ∘ q
local notation "Z"=> Sum.elim p' q

structure Inventory (e:Episode I B J) (F:Tier)(p':I→X)(q:B→X)(T:Tape X)(M:ℝ)(r d:ℕ): Prop where
 law : Rails e.joint e.vertices r (Sum.elim p' q) T F M
 le : e.Eligible r
 ready : Along T p' (Sum.elim p' q) F r e.spur M
 nn : 2 ≤ M
 mind : (r+1:ℝ) ≤ M
 cog : (d+3*r:ℝ) ≤ M

structure Pre (e:Episode I B J) (u:I→ℝ)(v:B→ℝ)(F:Tier)(C:ℝ) : Prop where
 row (i:I): (first e i).IsHomogeneous 1
 massive (i:I): F.valueOf v (stamp e i) ≤ F.value (u i) * C
 loft (i:I): free.valueOf v (stamp e i) ≤ C
 nn : 0 ≤ C

variable {F M p' q T r d}
variable (ha: Pre e u S F C)
lemma Integral (hc:Inventory e F p' q T M r d) {i j :ℕ}(h : i+j≤r) (hp : totalDegree p≤ d+3*i): F.valueOf (O.m ∘ q) (H n (beam e j p)) ≤ M^expansive d r * F.valueOf (O.m ∘ p') p:= calc
   _ ≤ F.gain Γ (e.floats (PowerSeries.monomial i p)) r := le_trans (worth_piece (beam e j p) n F (fun i=> O.sign (q i))) (by rw [boom (i:=i) e p]; exact F.now Γ (fun i=> O.sign (q i)) _ h)
   _ ≤ _ := (rough O hc.law hc.le hc.ready hc.nn hc.mind hc.cog (PowerSeries.monomial i p) (riseF p d hp)).trans_eq (by rw [ticket p F (by omega)])
-- repeated for ANY Tier pre. ratio gain ^n
include hu hv ha in
omit [Fintype I] [DecidableEq I] in
lemma diagonal (hp:p.IsHomogeneous n) : F.valueOf S (H n (beam e 0 p)) ≤ (2*C)^n * F.valueOf u p:= by
 rw [repeated p n ha.row (le_refl _) hp, if_pos rfl]; exact straight F hu hv p hp ha.nn ha.massive ha.loft
end YM.FormalOPE.RG10.GaugeGear
