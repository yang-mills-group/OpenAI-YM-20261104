import YangMills.PerturbativeMatching.NativeLattice
import YM.Extraction.Limits

set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory YM.Lattice
open scoped BigOperators Topology Matrix.Norms.Frobenius

variable {g : GaugeGroup}
abbrev wilsonFamily (C : YM.Family g.core) := PerturbativeMatching.wilsonFamily C

theorem energy_eq {l : ℕ+} (U : Configuration g l) :
    wilsonEnergy U = YM.Wilson.energy (G := g.core) U := by
  apply Finset.sum_congr rfl
  intro p _
  have face : faceValue U p = plaquette U p.1 p.2.val.1 p.2.val.2 := by
    simp only [faceValue, square, travel, Step.pos_read, Step.neg_read, Step.vec_neg,
      Step.vec_pos, mul_one, plaquette, step]
    congr 4 <;> abel_nf
  rw [show g.core.price (faceValue U p) = g.core.price (plaquette U p.1 p.2.val.1 p.2.val.2) from congrArg g.core.price face]
  rfl

theorem law_eq (l : ℕ+) (β : ℝ) :
    wilsonLaw g l β g.core.probHaar = YM.Wilson.law g.core l β := by
  simp only [wilsonLaw, energy_eq]
  rfl

variable (C : YM.Family g.core)
theorem moment_eq (N p : ℕ) {n : ℕ} (v : Fin n → C.book.Token)
    (x : Fin n → YM.Lattice.Site (C.side N p)) :
    (wilsonFamily C).finiteMoment N p v x = C.numeric N p v x := by
  unfold WilsonFamily.finiteMoment
  change (∫ U, _ ∂wilsonLaw g _ _ g.core.probHaar) = _
  rw [law_eq, C.num]
  rfl

theorem smear_eq (N p : ℕ) {n : ℕ} (v : Fin n → C.book.Token) (t : YM.Test n) :
    (wilsonFamily C).smear N p v t = YM.Extraction.Order.smears C N p v t := by
  simp only [WilsonFamily.smear, YM.Extraction.Order.smears, moment_eq]
  rfl

theorem fromWilson {S : YM.Table C.book} {s : YM.Extraction.Sequence}
    (h : (YM.Extraction.Order.mk .full s).Ordered C S) :
    (wilsonFamily C).Converges s (fun v x => S.read x v) := by
  intro n v t
  simp_rw [smear_eq]
  exact h.reads n v t

end YangMills
