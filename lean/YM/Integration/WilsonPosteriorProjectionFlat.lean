import YM.Integration.WilsonPosteriorProjectionClock
import YM.MSbar.Rolling.Skirt

/-! An arbitrarily high, genuine pointwise moving posterior match implies
the requested integer power for every individual outgoing wire component.
The constant below has no period, cutoff, location or realized trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionFlat
open Set Finset MeasureTheory Lattice Wilson RG Precision Tree Exterior Push.Uniform
open RG01.Kernel MSbar.Cacao MSbar.Rolling MSbar.Bulk LocalLTE.Weft
open WilsonPosteriorProjectionGerm WilsonPosteriorProjectionBank WilsonPosteriorProjectionStencil
open WilsonPosteriorProjectionWire WilsonPosteriorProjectionClock WilsonPosteriorProjectionCoefficient
open WilsonPosteriorProjectionPolarization
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

def tariff (G : Gauge) (C : ℝ) (M d : ℕ) (j : J M) :=
  ∑ u ∈ (rule j.val).support, |rule j.val u| * (cost M j * (1+ceiling G C (2*M+1) d u))

variable (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable (φ : Config G (H.S.side (m+1) n) → ℝ)

include sel hm in
theorem booked (g y C : ℝ) (p M d h : ℕ) (T : PowerSeries (Pot (Primary (H.S.side m n) G)))
    (degree : ∀ i≤p, (PowerSeries.coeff i T).totalDegree ≤ 2*M) (j : J M)
    (v : Fin j.val → Letter G (H.S.side m n)) (hg : 0<g) (g1 : g≤1)
    (hy : 0≤y) (ycap : y*g^2≤4) (hC : 0≤C)
    (penalty : |H.β N n (m+1)*H.levels.clock.kernel.penalty| * g^2 ≤ C)
    (order : 2*(2*M+1)+2*d+h+4*j.val ≤ 4*(2*M+1))
    (funded : Bounded (prior G (H.S.side (m+1) n))
      (fun (_ : (H.levels.clock.op m n).Choices) U => ((φ U : ℝ) : ℂ)) (y^d))
    (samples : ∀ u∈(rule j.val).support, ∀ i : J M, let Z := (g^4*probe M i) • studio v u
      |expect (H.levels.clock.op m n) (H.rep N n (m+1)) (postcard G (H.S.side m n) g Z) φ -
        reading p g T Z| ≤ g^(h+4*j.val)) :
    let X := fun i => display (impulse (v i))
    |(Tensor.coeff (fun Z => expect (H.levels.clock.op m n) (H.rep N n (m+1))
        (postcard G (H.S.side m n) g Z) φ) j.val 0) X -
       (Tensor.coeff (reading p g T) j.val 0) X| ≤ tariff G C M d j * g^h := by
  intro X
  let κ := H.β N n (m+1)*H.levels.clock.kernel.penalty
  have paid := at_wire H sel hm φ g (y^d) p M T degree j v (g^4) (g^(h+4*j.val)) (pow_pos hg _)
    funded (pow_nonneg hy _) samples
  let Δ := (Tensor.coeff (original H (N:=N) φ g) j.val 0) X - (Tensor.coeff (reading p g T) j.val 0) X
  change |Δ| ≤ tariff G C M d j * g^h
  apply (mul_le_mul_iff_left₀ (pow_pos (pow_pos hg 4) j.val)).mp
  rw [← abs_of_nonneg (pow_nonneg (pow_nonneg hg.le 4) j.val),← abs_mul]
  calc
    _ ≤ _ := paid
    _ ≤ ∑ u ∈ (rule j.val).support, |rule j.val u| * (cost M j *
        (g^(h+4*j.val) + ceiling G C (2*M+1) d u*g^(h+4*j.val))) := by
      apply sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun i _ => abs_nonneg _)
      exact add_le_add le_rfl (follows u (2*M+1) d h g y κ C hg g1 hy ycap hC penalty order)
    _ = _ := by
      unfold tariff
      have unit (u : Fin j.val → ℝ) : |rule j.val u| * (cost M j *
          (g^(h+4*j.val) + ceiling G C (2*M+1) d u*g^(h+4*j.val))) =
        (|rule j.val u| * (cost M j*(1+ceiling G C (2*M+1) d u)))*g^(h+4*j.val) := by ring
      simp_rw [unit]
      rw [← sum_mul,pow_add,pow_mul,abs_of_pos (pow_pos (pow_pos hg 4) j.val),mul_assoc]

end YM.Integration.WilsonPosteriorProjectionFlat

