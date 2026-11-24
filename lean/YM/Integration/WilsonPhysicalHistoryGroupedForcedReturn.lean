import YM.Integration.WilsonPhysicalHistoryCorrectionCarton
import YM.MergeProof.Pitch

/-! Keep the old quiet gas and its actual singleton coefficients when the
complete enrolled gas is presented to the lower conditional. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedForcedReturn
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedHard
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {Z : Census V}
  {P : Rep G n} {o : V → Site n} (A : Gallery T I o P Z) (w : V → ℝ) (positive : ∀ v, 0 < w v)

def single (t : T) (v : V) (box : Box n) (U : Config G n) :=
  (grouped P o A.K Finset.univ t box U).part (Z.fire v)

include positive in
theorem original {a h : ℝ} (expo : 0 ≤ a) (paid : A.K.Paid w P.p.B a h)
    (t : T) (box : Box n) (U : Config G n) :
    grouped P o A.K Finset.univ t box U =
      bar P.activities Z U box + Mach Z (fun v => single A t v box U) +
      WilsonPhysicalHistoryCorrectionCarton.forced A t box U := by
  let x := grouped P o A.K Finset.univ t box U
  have quiet : x.part Z.quiet = profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) box U := by
    rw [show x.part Z.quiet = _ from
      WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w positive Finset.univ expo paid t box U Z.quiet]
    simp only [Finset.mem_univ, if_true]
    apply tsum_congr
    intro i
    exact A.K.quiet t i.val U
  have mixed : octave x = WilsonPhysicalHistoryCorrectionCarton.forced A t box U := by
    ext s
    unfold WilsonPhysicalHistoryCorrectionCarton.forced
    rw [WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w positive _ expo paid t box U s]
    by_cases many : 2 ≤ s.val.card
    · rw [crest x s many]
      change (grouped P o A.K Finset.univ t box U).part s = _
      rw [WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w positive Finset.univ expo paid t box U s]
      simp [Finset.mem_filter, many]
    · rw [starlet x s (Nat.lt_of_not_ge many)]
      simp [Finset.mem_filter, many]
  calc
    _ = Poly.bead Z (x.part Z.quiet) + Mach Z (fun i => x.part (Z.fire i)) + octave x := ballots x
    _ = _ := by rw [mixed, quiet]; rfl

end YM.Integration.WilsonPhysicalHistoryGroupedForcedReturn
end

