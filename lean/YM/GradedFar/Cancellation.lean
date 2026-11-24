import YM.GradedFar.Expansion
/-!
# Homogeneous cancellation of the Far power

Crucially, the coefficient-wise OPS which had unconverted homogeneous price with
`T^(-W)` pays the **same power** as actually incurred by converting that Far label,
for full & replacement & remainder separately, when evaluated on each rotated Far basis tuple.
We prove the payment term by term. Singleton still has output weight decay; Basket
retains its OPE remainder power. Using these ChargeP bills in the actual operand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open MS XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ}
    {A : Arenas G} {ψ : ℝ → PowerSeries ℂ} {F : ℝ → Frames G} (H : Canon.Physical A ψ F)
    (law : Scale.Law A ψ F)
    {K : Set (Points n)} {S : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (u : Scan G n) (v : Scan G m)
local notation "FC" => Canon.FarCoefficients A
include H law hK hx hS hy

-- (We take law separately; in our application use specifically Hmatch.dilation.)
lemma cancel_full (j : LivesP v) (p h : ℕ) :
    ChargeP (p+1) 0 (fun (i : ↥K × ↥S) s => kPlay F (-s) v (decode v j) *
        party (install A) i.1.val (squeeze (-s) i.2.val) u (decode v j)) := by
  have hf := ChargeP.joint (charge_play law v (decode v j) (p+1) (I:=↥K × ↥S))
    (demand_full H hK hx hS hy u (decode v j) p h)
  simpa only [total_h, neg_add_cancel] using hf

omit hK hx in
lemma cancel_singleton (j : LivesP v) (q : Q G) (p : ℕ) :
    ChargeP (p+1) (heft q : ℝ) (fun (y : ↥S) s => kPlay F (-s) v (decode v j) *
      lonelyG (install A) (squeeze (-s) y.val) q (decode v j)) := by
  have hf := ChargeP.joint (charge_play law v (decode v j) (p+1) (I:=↥S))
    (demand_singleton H hS hy (decode v j) q p)
  rw [total_h, add_comm (heft q : ℝ), ← add_assoc, neg_add_cancel, zero_add] at hf
  exact hf

lemma cancel_ope (j : LivesP v) (p h : ℕ) :
    ChargeP (p+1) ((h:ℝ)+1) (fun (i : ↥K × ↥S) s => kPlay F (-s) v (decode v j) *
        Basket (install A) u (decode v j) (FC u i.1.val) h i.1.val (squeeze (-s) i.2.val)) := by
  have ho := demand_ope H hK hx hS hy u (decode v j) p h
  unfold RangeP at ho
  have hb := ChargeP.joint (charge_play law v (decode v j) (p+1) (I:=↥K × ↥S)) ho
  rw [total_h, add_comm ((h:ℝ)+1), ← add_assoc, neg_add_cancel, zero_add] at hb
  exact hb

variable {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : Through l d) (he : Through l e)
include law
/-- Log cost for the series after expanding each Far column and cancelling even at
mixed inserted tally orders. -/
lemma full_charge_basis (hu : InCaps d u) (hv : InCaps e v) (p : ℕ) :
    ChargeP (p+1) 0 (fun (i : ↥K × ↥S) s =>
      fullSeries A F (-s) hd he i.1.val i.2.val (loadScan u hu) (loadScan v hv)) := by
  simp_rw [fullSeries_expansion law _ hd he H.dimensions]; apply ChargeP.sum
  exact fun j _ => cancel_full H law hK hx hS hy u v j p 0

omit hK hx in
lemma replacement_charge_basis (q : Q G) (hh : h ≤ l) (hq : heft q ≤ h) (hv : InCaps e v) (p : ℕ) :
    ChargeP (p+1) (heft q : ℝ) (fun (y : ↥S) s =>
      replacementSeries A F (-s) hh he y.val (cap q hq) (loadScan v hv)) := by
  simp_rw [replacementSeries_expansion law _ he H.dimensions]; apply ChargeP.sum
  exact fun j _ => cancel_singleton H law hS hy v j q p

omit H hK hx hS hy

/-- Exact (F.O) series LHS after field conversion: same conversion in each term. -/
lemma ope_expansion_basis (hr : Regular A) (hu : InCaps d u) (hv : InCaps e v) (hh : h ≤ l)
    (x : Points n) (y : Points m) (η : ℝ) :
    fullSeries A F η hd he x y (loadScan u hu) (loadScan v hv) -
      ∑ q : Toon G h, FC u x (Dframe.flash q) * replacementSeries A F η hh he y (theory q) (loadScan v hv) =
    ∑ j : LivesP v, kPlay F η v (decode v j) * Basket (install A) u (decode v j)
      (FC u x) h x (squeeze η y) := by
  rw [fullSeries_expansion law η hd he hr]
  have hL (w : Scan G m) : Lamp (install A) h (squeeze η y) w (FC u x) =
      ∑ q : Toon G h, FC u x (Dframe.flash q) * lonelyG (install A) (squeeze η y) (Dframe.flash q) w :=
    (LampT (install A) h (squeeze η y) w (FC u x)).symm
  have hD (q : Toon G h) : replacementSeries A F η hh he y (theory q) (loadScan v hv) = _ :=
    replacementSeries_expansion law η he hr hh y (Dframe.flash q) v (size_le q) hv
  unfold Basket; simp_rw [hL, mul_sub]; rw [Finset.sum_sub_distrib]
  congr 1; simp_rw [hD, Finset.mul_sum]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm ..

include H hK hx hS hy
lemma ope_charge_basis (hu : InCaps d u) (hv : InCaps e v) (hh : h ≤ l) (p : ℕ) :
    ChargeP (p+1) ((h:ℝ)+1) (fun (i : ↥K × ↥S) s =>
      fullSeries A F (-s) hd he i.1.val i.2.val (loadScan u hu) (loadScan v hv) -
        ∑ q : Toon G h, FC u i.1.val (Dframe.flash q) *
          replacementSeries A F (-s) hh he i.2.val (theory q) (loadScan v hv)) := by
  simp_rw [ope_expansion_basis law u v hd he H.dimensions]; apply ChargeP.sum
  exact fun j _ => cancel_ope H law hK hx hS hy u v j p h

end YM.FVA2.GradedFar
