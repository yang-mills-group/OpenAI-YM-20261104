import YM.Integration.WilsonPhysicalHistoryGroupedGas
import YM.Integration.WilsonPhysicalHistoryCorrectionCarton
import YM.MergeProof.Pitch

/-! The nonconstant part of the enrolled regular logarithm has its true
singletons and its support-grouped mixed rows on every physical field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedRegularReturn
open Finset Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedLamps WilsonPhysicalHistoryGroupedClear
open WilsonPhysicalHistoryCorrectionCarton
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] [Countable I]
  {G : Gauge} {n : Side} {Z : Census V} {P : Rep G n} {o : V → Site n}
  (A : Gallery T I o P Z) (w : V → ℝ) (positive : ∀ v, 0 < w v)

include positive in
omit [Fintype V] [Countable I] in
private theorem total (entries : Set I) {a q : ℝ} (expo : 0 ≤ a) (paid : A.E.Paid w P.p.B a q)
    (t : T) (U : Config G n) :
    ∑ x, grouped A.E entries t x U = ∑' i, row A.E entries t i U := by
  have sum := (stored A.E w positive entries expo paid t).repair positive U
  have statement := (border A.E.ground sum.2).tsum_eq
  rw [tsum_fintype] at statement
  exact statement

def single (t : T) (v : V) (U : Config G n) :=
  (localLog A.E t U).part (Z.fire v)

include positive in
theorem original {a q : ℝ} (expo : 0 ≤ a) (paid : A.E.Paid w P.p.B a q)
    (t : T) (U : Config G n) :
    localLog A.E t U = Mach Z (fun v => single A t v U) + ∑ x, regular A t x U := by
  let localRows : Set I := {i | ¬ A.E.clear i}
  let mixedRows := regularRows A
  let localField := localLog A.E t U
  have localSum := (stored A.E w positive localRows expo paid t).repair positive U
  have mixedSum := (stored A.E w positive mixedRows expo paid t).repair positive U
  have groupedTotal := total A w positive mixedRows expo paid t U
  have quiet : localField.part Z.quiet=0 := by
    change (∑' i, row A.E localRows t i U).part Z.quiet=0
    rw [← total A w positive localRows expo paid t U, Poly.part_sum]
    exact Finset.sum_eq_zero fun x _ =>
      (WilsonPhysicalHistoryGroupedHealthy.fields A.E w positive localRows expo paid (fun _ h => h) t x).sil U
  have mixed : octave localField = ∑ x, regular A t x U := by
    ext s
    by_cases many : 2 ≤ s.val.card
    · rw [crest localField s many, show (∑ x, regular A t x U) = _ from groupedTotal]
      change (∑' i, row A.E localRows t i U).part s = _
      rw [Poly.share localSum.2 s, Poly.share mixedSum.2 s]
      apply tsum_congr
      intro i
      by_cases clear : A.E.clear i
      · simp [row, localRows, mixedRows, regularRows, clear]
      by_cases birth : s=A.E.mode i
      · have width : 2 ≤ (A.E.mode i).val.card := birth ▸ many
        simp [row, localRows, mixedRows, regularRows, clear, width]
      by_cases width : 2 ≤ (A.E.mode i).val.card <;>
        simp [row, localRows, mixedRows, regularRows, clear, width, Lamps.frame, Poly.part_send, birth]
    · rw [starlet localField s (Nat.lt_of_not_ge many), Poly.part_sum]
      symm
      apply Finset.sum_eq_zero
      intro x _
      apply not_not.mp
      intro active
      exact many (WilsonPhysicalHistoryGroupedHealthy.mixed A.E w positive mixedRows expo paid
        (fun _ h => h.2) t x U s active)
  calc
    _ = Poly.bead Z (localField.part Z.quiet) + Mach Z (fun v => localField.part (Z.fire v)) +
      octave localField := ballots localField
    _ = _ := by rw [quiet, mixed]; simp [Poly.bead, single, localField]

end YM.Integration.WilsonPhysicalHistoryGroupedRegularReturn
end

