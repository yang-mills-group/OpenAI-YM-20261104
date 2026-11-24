import YM.Integration.WilsonReportForwardTransfer
import YM.Integration.WilsonReportCoarseCumulant
import YM.Extraction.LatticeFamily

/-! The signed independent fine exterior in the connected original finite-regulator report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFineCumulant
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open WilsonReportForwardTransfer WilsonReportSpectatorModes WilsonReportMomentDifference
open Push.GridApprox
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V]
variable {W r D} {k N p : ℕ}

/-- The genuine nonlinear joint distribution: X is observed on the fine Wilson
field. The full product of the other marks is observed at one common sampled
coarse configuration through the original consecutive block kernels. -/
def measured (Γ : Census (Option V)) (hk : k ≤ N) (X : Config G (C.side N p)→ℂ)
    (F : V → Config G (C.side k p)→ℂ) : Poly Γ := Poly.inject fun s =>
  moment (C.beta N p) fun Z => (if none∈s.val then X Z else 1) *
    backTo C.path N p hk (fineJob F s.val.eraseNone) Z

private theorem measured_eq (Γ : Census (Option V)) (hC : C.Makes) (hk : k ≤ N)
    (X : Config G (C.side N p)→ℂ) (iX : Integrable X (law G (C.side N p) (C.beta N p)))
    (F : V → Config G (C.side k p)→ℂ) (hF : ∀ j, Envelope (F j)) :
    measured Γ hk X F = board (N:=N) Γ (WilsonReportForwardTransfer.exterior (N:=N) hk X) F := by
  ext s
  let t := fineJob F s.val.eraseNone
  have ht : Envelope t := Envelope.prodC s.val.eraseNone F (fun j _ => hF j)
  have fine : Integrable X (Therm.scene C.path N p N) := by rw [top hC N p]; exact iX
  change (∫ Z,(if none∈s.val then X Z else 1)*backTo C.path N p hk t Z ∂law G (C.side N p) (C.beta N p)) =
    ∫ U,(if none∈s.val then WilsonReportForwardTransfer.exterior (N:=N) hk X U else 1)*t U ∂Therm.scene C.path N p k
  rw [←top hC N p]
  by_cases active : none∈s.val
  · simpa only [active,if_true] using (joint hC hk le_rfl X fine t ht).symm
  · simpa only [active,if_false,one_mul] using Therm.retro hC.wilson hk le_rfl t ht

/-- Uniform connected price for the original microscopic spectator. The only
spectator fee is its own L¹ cost on the true fine Wilson law. -/
theorem purchased [Fintype V] (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (Γ : Census (Option V)) (d : V→ℕ) (t : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ hk : k<N, ∀ x : V→Site (C.side k p), ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ X : Config G (C.side N p)→ℂ, Integrable X (law G (C.side N p) (C.beta N p)) →
    ∀ s : Γ.Mode, none∈s.val →
    ‖(connected (measured Γ hk.le X (regularPack (N:=N) d x v))).part s-
      (connected (measured Γ hk.le X (ScenePack (N:=N) d x v))).part s‖ ≤
      (∫ Z, ‖X Z‖ ∂law G (C.side N p) (C.beta N p)) * WilsonReportMomentDifference.multiplicity Γ s *
        Real.exp (-((C.path.levels.budget k).B:ℝ)/2) := by
  filter_upwards [WilsonReportCoarseCumulant.purchased hG hC book citizen Γ d t,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k paid refs
  intro N p hk x v funds X iX s active
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  have fine : Integrable X (Therm.scene C.path N p N) := by rw [top hC N p]; exact iX
  have E := contract hC hk.le le_rfl X fine
  have h := paid N p hk x v funds _ E.1 s active
  have m := E.2
  rw [top hC N p] at m
  rw [measured_eq Γ hC hk.le X iX _ (fun j => wholeEnv H citizen (v j) (x j) hk (refs j)),
    measured_eq Γ hC hk.le X iX _ (fun j => cylinder_env (Strobe.bead_local H _ (v j) (refs j) hk.le _))]
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right m
    (WilsonReportSeparatedMoments.count_nonneg Γ s)) (Real.exp_nonneg _))

/-- A signed finite superposition of the exact microscopic coordinate products
used by Order.smears. Each slot keeps its own original grade and representative.
The coefficient array may include the actual spatial test and lattice weights. -/
def tested {n : ℕ} (tokens : Fin n→C.book.Token) (a : (Fin n→Site (C.side N p))→ℂ)
    (Z : Config G (C.side N p)) : ℂ :=
  ∑ y : Fin n→Site (C.side N p), a y*∏ j, C.seen (tokens j) (y j) Z

theorem admissible {n : ℕ} (tokens : Fin n→C.book.Token) (a : (Fin n→Site (C.side N p))→ℂ) :
    Integrable (tested tokens a) (law G (C.side N p) (C.beta N p)) := by
  apply integrable_finsetSum
  intro y _
  exact (C.integrableR tokens y).const_mul _

/-- For the actual smeared finite products the input is unconditional. All
mesh factors and all canceled signed labels remain inside the microscopic L¹ price. -/
theorem coordinates [Fintype V] (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (Γ : Census (Option V)) (d : V→ℕ) (t : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ hk : k<N, ∀ x : V→Site (C.side k p), ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ n : ℕ, ∀ tokens : Fin n→C.book.Token, ∀ a : (Fin n→Site (C.side N p))→ℂ,
    ∀ s : Γ.Mode, none∈s.val →
    ‖(connected (measured Γ hk.le (tested tokens a) (regularPack (N:=N) d x v))).part s-
      (connected (measured Γ hk.le (tested tokens a) (ScenePack (N:=N) d x v))).part s‖ ≤
      (∫ Z, ‖tested tokens a Z‖ ∂law G (C.side N p) (C.beta N p)) * WilsonReportMomentDifference.multiplicity Γ s *
        Real.exp (-((C.path.levels.budget k).B:ℝ)/2) := by
  filter_upwards [purchased hG hC book citizen Γ d t] with k h N p hk x v funds n tokens a s active
  exact h N p hk x v funds _ (admissible tokens a) s active

end YM.Integration.WilsonReportFineCumulant
end

