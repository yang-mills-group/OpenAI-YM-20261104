import YM.Integration.WilsonAddressedPublicPool
import YM.Integration.WilsonOriginalMicroscopicGuardedPage

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonAddressedPublicFineward
open Function Filter Finset Set Lattice RG Wilson Source Labels Extra.Histories Relay
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08
open WilsonOriginalMicroscopicGuardedNomination WilsonPositionProgramBlockedPublicExperiment
open WilsonAddressedPublicPool
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  {F : Final R.family f S} {l : Ultrafilter (ℕ×ℕ)} {D : ℕ} {g : ℝ → ℝ} {U : ℝ}
local notation "C₀" => R.family

theorem salary (η : ℝ) (ep : 0 < η) : ∃ j₀ : ℕ, ∀ {d j i N p : ℕ},
    j₀ ≤ j → (C₀).ref d ≤ j → j ≤ i → i ≤ N → ∀ y : (C₀).label d,
    ((C₀).labels.level d).coeffSize (deposited R d N p i y).x ≤ hike C₀ j i η *
      ((C₀).labels.level d).coeffSize (deposited R d N p j y).x := by
  obtain ⟨j₀,step⟩ := eventually_atTop.mp (factor_large C₀ η ep)
  refine ⟨j₀,?_⟩
  intro d j i N p late ref ji live y
  have cal := R.makes.calibrated d N p ((ref.trans ji).trans live)
  induction i, ji using Nat.le_induction with
  | base => rw [hike_id,one_mul]
  | succ i hi ih =>
    let z := ((C₀).factory d N p).terminal.symm y
    let h (i : ℕ) := ((C₀).labels.level d).coeffSize (deposited R d N p i y).x
    have down := cal.back i (ref.trans hi) live z
    change h (i+1) ≤ stock C₀ (i+1)*h i at down
    have pos := ((C₀).path.levels.params (i+1)).columns_ge
    have short := (step i (late.trans hi)).2
    have fare : stock C₀ (i+1) ≤ (factor C₀ i)^η := by
      change 1 ≤ stock C₀ (i+1) at pos
      linarith
    have old := ih (Nat.le_trans (Nat.le_succ i) live)
    refine down.trans ((mul_le_mul_of_nonneg_right fare (size_nonneg _ _)).trans ?_)
    refine (mul_le_mul_of_nonneg_left old (Real.rpow_nonneg (zero_lt_one.trans (factor_positive C₀ i)).le _)).trans_eq ?_
    rw [hike_succ];ring

theorem original (simple : G.Simple) (A : Pool R (l:=l) F D g U) (η : ℝ) (ep : 0 < η) :
    ∀ᶠ r in trail, ∀ a : Fin (D+1), ∀ (v : S.Field a.val) (i N p : ℕ),
    A.j r ≤ i → i ≤ N → A.j r < N →
    let y := A.field a r v (N,p)
    let q := deposited R a.val N p i y
    let W := (C₀).path.rep N p i
    let B := hike C₀ (A.j r) i η * budget R F a.val (A.ρ r) (A.j r) (A.B r) v
    q.Format 0 (C₀).params W ∧ q.remBound 0 W (safety C₀ i) (stock C₀ i * B) ∧
      ((C₀).labels.level a.val).coeffSize q.x ≤ B ∧
      ((C₀).labels.level a.val).coeffSize (page a.val p i q) ≤ 2*B := by
  obtain ⟨j₀,fee⟩ := salary R η ep
  have opens : ∀ a : Fin (D+1), ∀ᶠ j : ℕ in atTop, ∀ p, Opened C₀ a.val j p :=
    fun a => open_late C₀ simple a.val
  have joint := (Filter.eventually_all).2 opens
  obtain ⟨k,gate⟩ := eventually_atTop.mp joint
  filter_upwards [A.standing,A.enters.eventually_ge_atTop (max j₀ k)] with r heard late
  intro a v i N p ji live nonbare y q W B
  have pre := (heard a).2 v
  have openj := gate (A.j r) (le_trans (le_max_right _ _) late) a p
  have oi := gate i ((le_trans (le_max_right _ _) late).trans ji) a p
  have fine := fee (p:=p) (le_trans (le_max_left _ _) late) openj.post ji live y
  have size : ((C₀).labels.level a.val).coeffSize q.x ≤ B :=
    fine.trans (mul_le_mul_of_nonneg_left (pre.1 N p nonbare) (hike_pos C₀ _ _ _).le)
  let z := ((C₀).factory a.val N p).terminal.symm y
  have cal := R.makes.calibrated a.val N p (oi.post.trans live)
  have stockpos : 0 ≤ stock C₀ i := zero_le_one.trans ((C₀).path.levels.params i).columns_ge
  refine ⟨cal.format i oi.post live z,rem_mono (cal.cap i oi.post live z) ?_,size,?_⟩
  · exact mul_le_mul_of_nonneg_left ((size_core _ _).trans size) stockpos
  · exact (size_gap a.val N p i R.makes oi live z).1.trans (mul_le_mul_of_nonneg_left size zero_le_two)

end YM.Integration.WilsonAddressedPublicFineward
end
