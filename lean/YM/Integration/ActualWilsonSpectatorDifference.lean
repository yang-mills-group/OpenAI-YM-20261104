import YM.Integration.ActualWilsonForcedSlots
import YM.Integration.SelectedCofactorProductHaar

/-! The signed change of the unnormalized spectator minor, paired at the
same original Wilson marked slot. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonSpectatorDifference

open Function Set Finset Lattice Wilson RG Marker Source Labels
open Extra.Histories FullQLocal Trace.Physical Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato SelectedCofactorProductHaar
open ActualWilsonGraphReclosure ActualWilsonForcedSlots
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}

/-- The native scalar pinned minor is exactly the ordinary dressed spectator
product. -/
theorem coat_pinned (X : Rep G n) (i : ℕ) (s : Finset ℕ) (U : Config G n) :
    coat X i s U = SelectedCofactorCancellation.pinnedVacuum X U i s := by
  simp only [coat, SelectedCofactorCancellation.pinnedVacuum,
    NativeCoveredCofactorLocalUpdate.admitted_iff, and_comm]

/-- Absolute summability of all original marked partners and vacuum minors,
using the selected carrier's actual activity bound. -/
theorem packet_dom {p : BudgetPoint} {w : ℝ} {X : Rep G n}
    (hX : X.activities.KBound p w) {y : ℕ → Config G n → ℂ} (hy : Dominated y) :
    Dominated fun a : ℕ × Finset ℕ => fun U => y a.1 U * coat X a.1 a.2 U := by
  obtain ⟨k,hk,hK⟩ := Activities.K_total hX
  obtain ⟨r,hr,hr'⟩ := hy
  let a (i : ℕ) := r i + k i
  have hr0 (i : ℕ) : 0 ≤ r i := (norm_nonneg _).trans (hr' i 1)
  have ha (i : ℕ) : 0 ≤ a i := add_nonneg (hr0 i) (hK i).1
  have hsum : Summable a := hr.add hk
  refine ⟨packetWeight a, packetWeight_summable ha hsum,?_⟩
  rintro ⟨i,s⟩ U
  change ‖y i U * coat X i s U‖ ≤ packetWeight a (i,s)
  by_cases hh : i ∈ s ∧ X.activities.admissible X.p U s
  · rw [coat, if_pos hh, norm_mul, norm_prod]
    have hb j : ‖(X.activities.K j U : ℂ)‖ ≤ a j :=
      (Complex.norm_real _).trans_le (((hK j).2 U).trans (le_add_of_nonneg_left (hr0 j)))
    have hm : (∏ j ∈ s.erase i, ‖(X.activities.K j U : ℂ)‖) ≤ ∏ j ∈ s.erase i, a j :=
      Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hb j)
    apply (mul_le_mul ((hr' i U).trans (le_add_of_nonneg_right (hK i).1)) hm
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (ha i)).trans_eq
    rw [Finset.mul_prod_erase s a hh.1, packetWeight, if_pos hh.1]
  rw [coat, if_neg hh, mul_zero, norm_zero]
  unfold packetWeight
  split
  · exact Finset.prod_nonneg (fun j _ => ha j)
  exact le_rfl

theorem rows {p : BudgetPoint} {w : ℝ} {X : Rep G n} (hX : X.activities.KBound p w)
    (q : Coefficient F n) (hq : Dominated q.forced) (U : Config G n) :
    Summable (fun i => q.forced i U * dressed X i U) ∧
    ∑' s, q.marked X s U = ∑' i, q.forced i U * dressed X i U := by
  have h : Summable (fun a : ℕ × Finset ℕ => q.forced a.1 U * coat X a.1 a.2 U) :=
    (packet_dom hX hq).summable U
  have hf (i : ℕ) : (∑' s, q.forced i U * coat X i s U) = q.forced i U * dressed X i U :=
    tsum_mul_left (f := fun s => coat X i s U) (a := q.forced i U)
  have hs : Summable (fun i : ℕ => ∑' s : Finset ℕ, q.forced i U * coat X i s U) := h.prod
  refine ⟨hs.congr hf,?_⟩
  calc
    ∑' s, q.marked X s U = ∑' s, ∑' i, q.forced i U * coat X i s U :=
      tsum_congr (fun s => marked_as q X s U)
    _ = ∑' i, ∑' s, q.forced i U * coat X i s U := by
      exact Summable.tsum_comm (f := fun i s => q.forced i U * coat X i s U) h
    _ = _ := tsum_congr hf

/-- A fieldwise identity for the entire change in the represented Wilson
density. The same retained signed row multiplies the difference of the two
whole spectator factors at its original and rebooked address. -/
theorem paired (R : Run G) (hG : G.Simple) {N p i : ℕ} (hi : i ≤ N)
    (X : PhysicalCarrier R.family N p i) (he : X.rep.eval = (R.family.path.rep N p i).eval)
    {b : BudgetPoint} {w r : ℝ} (hk : X.rep.activities.KBound b w)
    (q : store R.family d p i) (hf : q.Format 0 R.family.params X.rep)
    (hr : q.remBound 0 X.rep (safety R.family i) r) (U : Config G (R.family.side i p)) :
    let Y := R.family.path.rep N p i
    let e := address X.rep (OriginalForcedAddresses.actual_keeper R hG N i p hi)
    let W := original R hG hi X q
    Summable (fun j => q.forced j U *
      ((Real.exp (X.rep.exponent U) : ℂ) * dressed X.rep j U -
        (Real.exp (Y.exponent U) : ℂ) * dressed Y (e j) U)) ∧
    q.density 0 (R.family.localSection d) X.rep U - value d N p i W U =
      ∑' j, q.forced j U *
        ((Real.exp (X.rep.exponent U) : ℂ) * dressed X.rep j U -
          (Real.exp (Y.exponent U) : ℂ) * dressed Y (e j) U) := by
  intro Y e W
  have hq := rows hk q (rem_dominated hr) U
  have hW := rows (X := Y) (R.makes.wilson.represents N p i hi).good.labels.boundK W
    (rem_dominated (original_price R hG hi X q hf hr).1.2) U
  let f (j : ℕ) := W.forced j U * dressed Y j U
  have he0 (j : ℕ) (hj : j ∉ Set.range e) : f j = 0 := by
    change (place X.rep _ q).forced j U * dressed Y j U = 0
    rw [off_slot _ q hj]
    exact zero_mul _
  have hsup : Function.support f ⊆ Set.range e := by
    intro j hj
    by_contra hnot
    exact hj (he0 j hnot)
  have hon (j : ℕ) : f (e j) = q.forced j U * dressed Y (e j) U := by
    change (place X.rep _ q).forced (address X.rep _ j) U * _ = _
    rw [on_slot]
  have hs : Summable (fun j => q.forced j U * dressed Y (e j) U) :=
    (show Summable (f ∘ e) from hW.1.comp_injective e.injective).congr hon
  have ht : (∑' j, f j) = ∑' j, q.forced j U * dressed Y (e j) U :=
    (e.injective.tsum_eq hsup).symm.trans (tsum_congr hon)
  let α : ℂ := Real.exp (X.rep.exponent U)
  let β : ℂ := Real.exp (Y.exponent U)
  have hleft := hq.1.mul_left α
  have hright := hs.mul_left β
  have hpair (j : ℕ) : α*(q.forced j U * dressed X.rep j U) -
      β*(q.forced j U * dressed Y (e j) U) =
      q.forced j U * (α*dressed X.rep j U - β*dressed Y (e j) U) := by ring
  refine ⟨(hleft.sub hright).congr hpair,?_⟩
  rw [original_difference R hG hi X q he U]
  change α * (∑' s, q.marked X.rep s U) - β * (∑' s, W.marked Y s U) = _
  rw [hq.2, hW.2]
  change α * (∑' j, q.forced j U * dressed X.rep j U) - β * (∑' j, f j) = _
  rw [ht, ← tsum_mul_left, ← tsum_mul_left, ← hleft.tsum_sub hright]
  exact tsum_congr hpair

end YM.Integration.ActualWilsonSpectatorDifference
