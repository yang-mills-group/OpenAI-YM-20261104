import YangMills.WilsonProof.NativeSupport.HierarchySpec

import YangMills.WilsonProof.NativeSupport.YangMills.VacuumReconstruction

/-! Ward stress and Maxwell tests on the reconstructed vacuum fields. -/

set_option autoImplicit false

noncomputable section

namespace YangMills

open Function Filter Set MeasureTheory

open scoped Topology BigOperators InnerProductSpace Distributions Classical ContDiff

namespace Reconstruction

variable {g : GaugeGroup} {C : WilsonFamily g}

theorem PhaseSource.stressHermitian {T : Hierarchy C} {i : T.Character}
    {H : HilbertSpace} {A : WightmanTheory H T.labels} (P : PhaseSource T i H A)
    (a b : Axis) (f : TestFunction) (u v : A.fields.domain) :
    inner ℂ (A.fields.field (minkowskiStress T a b) f u).1 v.1 =
      inner ℂ u.1 (A.fields.field (minkowskiStress T a b) (conjugateTest f) v).1 := by
  simpa only [P.stressAdjoint] using P.axioms.w1.adjoint (minkowskiStress T a b) f u v

def SelectedMaxwellJets (B : Maxwell.Reference g) (T : Hierarchy C)
    (X : T.MaxwellScaling B) : Prop :=
  ∀ (n j : ℕ) (q : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (K : Set (Points n)), IsCompact K →
    K ⊆ WilsonFamily.separated n → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun z => T.correlation (some T.selected) (fun i => if marked i then
          ⟨4, ((X.r k ^ 4 : ℝ) : ℂ) • T.stress (ab i).1 (ab i).2⟩ else
          ⟨(q i).1, X.frame k _ (q i).2⟩) (X.r k • z)) x -
        iteratedFDeriv ℝ j (fun z => B.moment z (fun i => if marked i then
          (B.stress (ab i).1 (ab i).2).val else (q i).2.val)) x‖ ≤ ε

end Reconstruction

structure WilsonReconstruction {g : GaugeGroup} {C : WilsonFamily g}
    (B : Maxwell.Reference g) (T : Hierarchy C) : Prop where
  tables : Reconstruction.TableLaws T
  phases : Nonempty (Reconstruction.Phases T)
  maxwell : ∃ X : T.MaxwellScaling B, Reconstruction.SelectedMaxwellJets B T X

end YangMills
