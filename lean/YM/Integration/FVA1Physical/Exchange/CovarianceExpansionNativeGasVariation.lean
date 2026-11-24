import YM.Push.ABSOLUTE_SUMS.Path
import YM.Integration.KBoundGas
import YM.Integration.FVA1Physical.Sources.Round2.NativeGasRoster
import YM.Push.GRID_APPROXIMATION.Hit

/-! Scoped replay of the earlier clean one-bond scalar gas bound on the
exact existing activity family: only the native roster bill and physical
cover-distance theorem are needed by its source proofs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction.ActualGas
open Finset Lattice RG Wilson Push.AbsoluteSums Push.GridApprox.Attach
open YM.Integration.FVA1Physical.Round2.Curvature.Tariff.Native
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{p:BudgetPoint}
theorem cover_of_flag_outside {a r : ℕ} {X S : Support n} {o z : Site n}
    (ho : o ∈ X) (hs : o ∈ S) (hz : z ∈ X) (hout : z ∉ halo (r * leg a) S) :
    r ≤ coverNumber a X := by
  have hsep : r * leg a ≤ separation z o := le_of_not_ge fun h =>
    hout (halo_spec.mpr ⟨o, hs, (separation_comm o z).le.trans h⟩)
  calc
    r = (r * leg a) / leg a := (Nat.mul_div_cancel r (leg_pos _)).symm
    _ ≤ separation z o / leg a := Nat.div_le_div_right hsep
    _ ≤ _ := distance_charge X a z o hz ho

variable (A:Activities G n)(e:Edge (Site n))(U V:Config G n)
def sameOffBond : Prop := ∀ l, l ≠ e → U l = V l

theorem flags_at_bond {t : ℝ} (off : sameOffBond e U V)
    (hu : e.1 ∉ flags t U) (hv : e.1 ∉ flags t V) : flags t U = flags t V := by
  have move (X Y : Config G n) (eq : sameOffBond e X Y) (good : e.1 ∉ flags t X) :
      flags t X ⊆ flags t Y := by
    intro z hz
    obtain ⟨f,foot,bad⟩ := (flags_spec t X z).mp hz
    have away : e.1 ∉ touched f := fun seen => good ((flags_spec t X e.1).mpr ⟨f,seen,bad⟩)
    have stable : faceValue X f = faceValue Y f := by
      apply travel_local
      intro edge fromSite _
      exact eq edge (fun id => away (id ▸ List.mem_toFinset.mpr fromSite))
    exact (flags_spec t Y z).mpr ⟨f,foot,stable ▸ bad⟩
  exact Subset.antisymm (move U V off hu) (move V U (fun l ne => (off l ne).symm) hv)

theorem variable_owner_endpoints (law : A.ForcedFamily p) (off : sameOffBond e U V)
    (flags_id : flags p.threshold U = flags p.threshold V) (j : ℕ) (moves : A.K j U ≠ A.K j V) :
    e.1 ∈ (A.forced j).support ∧ e.1+step e.2 ∈ (A.forced j).support := by
  by_contra h
  apply moves
  apply law.reads j U V _ (congrArg ((A.forced j).support ∩ ·) flags_id)
  intro l src dst
  exact off l (fun eq => h ⟨eq ▸ src,eq ▸ dst⟩)

theorem changed_forced_cover (law : A.ForcedFamily p) (off : sameOffBond e U V)
    (flags_id : flags p.threshold U = flags p.threshold V) (r : ℕ)
    (healthy : Healthy p.threshold (halo (r*leg p.B) {e.1}) U)
    (j : ℕ) (moves : A.K j U ≠ A.K j V) : r ≤ coverNumber p.B (A.forced j).support := by
  have at_bond := (variable_owner_endpoints A e U V law off flags_id j moves).1
  obtain ⟨z,owned⟩ := (A.forced j).inventory_ne
  have alarm : z ∈ flags p.threshold U := by
    by_cases onU : A.K j U = 0
    · have onV : A.K j V ≠ 0 := by simpa only [onU,ne_eq,eq_comm] using moves
      rw [flags_id]
      exact (mem_inter.mp ((law.permit j V onV).1.symm ▸ owned)).2
    exact (mem_inter.mp ((law.permit j U onU).1.symm ▸ owned)).2
  exact cover_of_flag_outside at_bond (mem_singleton_self _)
    ((A.forced j).inventory_sup owned) (fun near => Finset.disjoint_left.mp healthy near alarm)

variable {e U V}
theorem varying_roster_reaches (law : A.ForcedFamily p) (e : Edge (Site n)) (U V : Config G n)
    (off : sameOffBond e U V) (inv : flags p.threshold U = flags p.threshold V)
    (r : ℕ) (healthy : Healthy p.threshold (halo (r*leg p.B) {e.1}) U) (s : Finset ℕ)
    (varies : A.gasOccurrence p s U ≠ A.gasOccurrence p s V) :
    ∃ j ∈ s, r ≤ coverNumber p.B (A.forced j).support := by
  by_contra missing
  have equal (j : ℕ) (hj : j ∈ s) : A.K j U = A.K j V := by
    by_contra changes
    exact missing ⟨j,hj,changed_forced_cover A e U V law off inv r healthy j changes⟩
  apply varies
  have ok : A.admissible p U s = A.admissible p V s := by
    simp only [Activities.admissible,inv]
  unfold Activities.gasOccurrence
  rw [ok]
  split
  · exact prod_congr rfl equal
  · rfl

theorem signed_gas_roster_price {w δ : ℝ} (law : A.ForcedFamily p) (paid : A.KBound p w)
    (small : w ≤ 1) (hd : 0 ≤ δ) (e : Edge (Site n)) (r : ℕ) (D : Support n)
    (U V : Finset ℕ → Config G n) (before : ∀ s, flags p.threshold (U s) = D)
    (after : ∀ s, flags p.threshold (V s) = D) (off : ∀ s, sameOffBond e (U s) (V s))
    (healthy : ∀ s, Healthy p.threshold (halo (r*leg p.B) {e.1}) (U s)) :
    SumBudget (fun s => Real.exp ((p.supportExponent-δ)*(∑ i ∈ s,(coverNumber p.B (A.forced i).support:ℝ))) *
      ‖A.gasOccurrence p s (U s)-A.gasOccurrence p s (V s)‖)
      (Real.exp (-δ*r)*((if D=∅ then 1 else w)+(if D=∅ then 1 else w))) := by
  have left := native_gas_roster A small paid D U before
  have right := native_gas_roster A small paid D V after
  have allPaid := budget_scale (Real.exp_pos (-δ*r)).le (budget_plus left right)
  apply budget_mono allPaid
  · intro s; exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  intro s
  by_cases eqn : A.gasOccurrence p s (U s) = A.gasOccurrence p s (V s)
  · calc
      _ = 0 := by rw [eqn,sub_self,norm_zero,mul_zero]
      _ ≤ _ := allPaid.1 s
  obtain ⟨i,hi,reach⟩ := varying_roster_reaches A law e (U s) (V s) (off s)
    ((before s).trans (after s).symm) r (healthy s) s eqn
  let size : ℝ := ∑ j ∈ s,(coverNumber p.B (A.forced j).support:ℝ)
  have length : (r:ℝ) ≤ size := (Nat.cast_le.mpr reach).trans
    (single_le_sum (fun j _ => Nat.cast_nonneg (coverNumber p.B (A.forced j).support)) hi)
  have normed : rosterWeight A p s = Real.exp (p.supportExponent*size) := by
    unfold rosterWeight size; rw [Finset.mul_sum,Real.exp_sum]
  have reserve : Real.exp ((p.supportExponent-δ)*size) ≤ Real.exp (-δ*r)*rosterWeight A p s := by
    rw [normed,←Real.exp_add,Real.exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_left length hd]
  change Real.exp ((p.supportExponent-δ)*size)*_ ≤ Real.exp (-δ*r) *
    (rosterWeight A p s * ‖A.gasOccurrence p s (U s)‖ + rosterWeight A p s * ‖A.gasOccurrence p s (V s)‖)
  exact (mul_le_mul reserve (norm_sub_le ..) (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (roster_weight_nonneg A p s))).trans_eq (by ring)

theorem actual_gas_bond_falloff {w : ℝ} (law : A.ForcedFamily p) (paid : A.KBound p w)
    (small : w ≤ 1) (e : Edge (Site n)) (r : ℕ) (U V : Config G n) (off : sameOffBond e U V)
    (healthy : Healthy p.threshold (halo (r*leg p.B) {e.1}) U) (after : e.1 ∉ flags p.threshold V) :
    ‖A.gas p U-A.gas p V‖ ≤ 2*w*Real.exp (-p.supportExponent*r) := by
  have before : e.1 ∉ flags p.threshold U := disjoint_left.mp healthy (halo_subset _ _ (mem_singleton_self _))
  have same := flags_at_bond e U V off before after
  by_cases noFlags : flags p.threshold U = ∅
  · rw [A.gas_one p noFlags,A.gas_one p (same.symm.trans noFlags),sub_self,norm_zero]
    obtain ⟨_,_,site⟩ := paid
    exact mul_nonneg (mul_nonneg zero_le_two (budget_nonneg (site e.1))) (Real.exp_pos _).le
  have price := signed_gas_roster_price A law paid small p.exponent_pos.le e r (flags p.threshold U)
    (fun _ => U) (fun _ => V) (fun _ => rfl) (fun _ => same.symm) (fun _ => off) (fun _ => healthy)
  simp only [sub_self,zero_mul,Real.exp_zero,one_mul,if_neg noFlags] at price
  have series := Activities.gasSeries_of_KBound paid
  change ‖(∑' s,A.gasOccurrence p s U)-(∑' s,A.gasOccurrence p s V)‖ ≤ _
  rw [←(series.summable U).tsum_sub (series.summable V)]
  exact (norm_tsum_le_tsum_norm price.2.1).trans (price.2.2.trans_eq (by ring))

end YM.Integration.FVA1Physical.Exchange.ShieldedAction.ActualGas
