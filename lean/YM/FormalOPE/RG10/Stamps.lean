import YM.FormalOPE.RG10.InversionTop

/-!
# Orbit real stamps for the two-insertion test (coupling powers included)

Use `Stamp` at the orbit regulator for real **even-gauge invariant** observables with smooth
saddle germ. Keep the negative degree from engineering rescaling with a proof they enter that
late. Finite root sums, faces, clovers, probes, normalized field frame components etc may use
these calculations, including contact-producing overlap products before subtraction. This is not
defining any continuum field basis. Hand-off to the common-lattice producers: use the identical
`SectionData`/`fieldAt` (or stencils & provide proof) here. Products use pre-log, jointly.
-/
set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10.InversionTop
open Gauge Lattice PertExtension PertExtension.Chart PertExtension.Orb Wilson PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open scoped BigOperators Topology ContDiff Classical

variable {G : Gauge} {n : Side} (hn : Even n.val)
local notation "P" => tray G

namespace Uses

lemma pre_mul {O Q : Config G n → ℝ} (hp : PreTest O) (hq : PreTest Q) : PreTest (O*Q) where
  gauge u hu x := by simp [hp.gauge u hu, hq.gauge u hu]
  curved := ⟨hp.curved.boundedness.mul hq.curved.boundedness, hp.curved.germ.mul hq.curved.germ⟩
  continuous := hp.continuous.mul hq.continuous

/-- Realizations of coupling-shifted marks. `A` can be a general Taylor computation (e.g.
calculated analytically), but its use requires an identity of all potential jets in this chart.
-/
def AtCoupling (O : Config G n → ℝ) (d : ℕ) (A : Kernel (Unit × Dir G n)) :=
  delay d A = raw (restrictedO O)

lemma combine {O Q : Config G n → ℝ} (ho : PreTest O) (hq : PreTest Q) {dO dQ A B}
    (hO : AtCoupling O dO A) (hQ : AtCoupling Q dQ B) :
    AtCoupling (O*Q) (dO + dQ) (A*B) := by
  unfold AtCoupling
  rw [delay_mul, hO, hQ, ← raw_mul ho.curved hq.curved]; rfl

lemma advance {O : Config G n → ℝ} (ho : PreTest O) {d A} (h : AtCoupling O d A) :
    into (PowerSeries.mk (diag (restrictedO O))) =
      X ^ d * (feed hn).step (vertices G n) A := by
  rw [← FlatFeed.step_delay, ← tree_agreement hn ho.curved, h]

include hn in
lemma subleading {O : Config G n → ℝ} (ho : PreTest O) {d A} (h : AtCoupling O d A) (k : ℕ) (hk : k < d) :
    diag (restrictedO O) k = 0 := by
  have H := congr_arg (PowerSeries.coeff k) (advance hn ho h)
  rw [into_coeff, coeff_X_pow_mul', if_neg hk.not_ge, coeff_mk] at H
  exact_mod_cast H

lemma grade {O : Config G n → ℝ} (ho : PreTest O) {d A} (h : AtCoupling O d A) (k : ℕ) :
    coeff k ((feed hn).step (vertices G n) A) = diag (restrictedO O) (d+k) := by
  have H := congr_arg (PowerSeries.coeff (d+k)) (advance hn ho h)
  rw [into_coeff, coeff_mk, coeff_X_pow_mul', if_pos (by omega), show d+k-d=k by omega] at H
  exact H.symm

/-- Contact included on the regulated side. This is at this **fixed** regulator only. -/
lemma inversionFormula {O : Config G n → ℝ} (ho : PreTest O) {d A} (h : AtCoupling O d A) :
    Aspiration (fun r : ℝ => (r⁻¹)^d * preExpectation O r)
      (fun i => (coeff i ((feed hn).step (vertices G n) A)).re) := by
  simp_rw [grade hn ho h, Complex.ofReal_re]
  exact (before_tree_formula hn (traySpec G) ho).shift (subleading hn ho h)

lemma paid {O : Config G n → ℝ} (ho : PreTest O) {d A} (h : AtCoupling O d A) :
    (feed hn).Funded ((vertices G n).weight * A) := by
  apply FlatFeed.funded_of_delay _ _ d
  have hz : delay d ((vertices G n).weight * A) = (vertices G n).weight * delay d A := by
    simpa only [zero_add, delay_zero] using delay_mul (vertices G n).weight A 0 d
  rw [hz, h]
  exact funded hn ho.curved

@[simp] lemma funded_vacuum : (feed hn).Funded (vertices G n).weight := by
  simpa only [raw_one, mul_one] using (funded hn (G:=G) (O:=1) one_test)
end Uses

/-- One real mark at the formal Wilson regulator (nominal factor `g^{-slots}`). This can itself
contain products e.g. from a nonlinear output column. Geometry/far estimate inputs are separate
from this finite-regulator all-order definition.
-/
structure Stamp (G : Gauge) (n : Side) where
  stencil : Config G n → ℝ
  test : PreTest stencil
  slots : ℕ
  cleared : ∀ k, k < slots → row k (raw (restrictedO stencil)) = 0

namespace Stamp
variable (A : Stamp G n) (B : Stamp G n)

def couplingMark : Kernel (Unit × Dir G n) := fun x => lower A.slots (raw (restrictedO A.stencil) x)

lemma atCoupling : Uses.AtCoupling A.stencil A.slots A.couplingMark := by
  funext x; apply PowerSeries.ext; intro k
  unfold delay
  rw [coeff_X_pow_mul']
  split
  next h =>
    unfold couplingMark lower
    rw [coeff_mk, Nat.add_sub_of_le h]
  next h => exact (congr_fun (A.cleared k (Nat.lt_of_not_ge h)) x).symm

/-- This identity with the independent Wilson definition includes coincidences at this fixed
lattice. Does not pertain to continuum coincidence. -/
lemma two_coefficient (k : ℕ) : coeff k ((feed hn).step (vertices G n) (A.couplingMark * B.couplingMark)) =
    (diag (restrictedO (A.stencil * B.stencil)) (A.slots + B.slots + k) : ℝ) :=
  Uses.grade hn (Uses.pre_mul A.test B.test) (Uses.combine A.test B.test A.atCoupling B.atCoupling) k

end Stamp
end YM.FormalOPE.RG10.InversionTop
