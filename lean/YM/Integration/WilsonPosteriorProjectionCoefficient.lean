import YM.Integration.WilsonPosteriorProjectionBank
import YM.Integration.WilsonPosteriorProjectionGerm
import YM.Integration.WilsonPosteriorProjectionWireRoom

/-! The signed mixed component at a prescribed tuple of sites, axes and
colors: original normalized Haar kernel versus the independent, complete
finite clock reading. No measured or independent jet is supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionCoefficient
open Finset Set MeasureTheory Lattice Wilson RG Precision Tree Exterior Push.Uniform
open RG01.Kernel RG01.Kernel.Wheel LocalLTE.Weft MSbar.Cacao
open WilsonPosteriorProjectionRay WilsonPosteriorProjectionStencil WilsonPosteriorProjectionTaylor
open WilsonPosteriorProjectionWire WilsonPosteriorProjectionWireRoom WilsonPosteriorProjectionPolarization
open WilsonPosteriorProjectionGerm WilsonPosteriorProjectionHaar WilsonPosteriorProjectionBank
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

def response {r : ℕ} (G : Gauge) (κ b g : ℝ) (q : ℕ) (u : Fin r → ℝ) :=
  ((1+(abs κ)*tariff G)*(1+(abs g)*slots u))^q * |compensation G q (invoice q b) (1+2*1)|

variable (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable (φ : Config G (H.S.side (m+1) n) → ℝ)

include sel hm in
theorem at_wire (g b : ℝ) (p M : ℕ) (T : PowerSeries (Pot (Primary (H.S.side m n) G)))
    (degree : ∀ i≤p, (PowerSeries.coeff i T).totalDegree ≤ 2*M) (j : J M)
    (v : Fin j.val → Letter G (H.S.side m n)) (t ε : ℝ) (ht : 0<t)
    (funded : Bounded (prior G (H.S.side (m+1) n))
      (fun (_ : (H.levels.clock.op m n).Choices) U => ((φ U : ℝ) : ℂ)) b) (hb : 0≤b)
    (samples : ∀ u∈(rule j.val).support, ∀ i : J M,
      let Z := (t*probe M i) • studio v u
      |original H (N:=N) φ g Z - reading p g T Z| ≤ ε) :
    let X := fun i => display (impulse (v i))
    let κ := H.β N n (m+1) * H.levels.clock.kernel.penalty
    |((Tensor.coeff (original H (N:=N) φ g) j.val 0) X -
        (Tensor.coeff (reading p g T) j.val 0) X)*t^j.val| ≤
      ∑ u ∈ (rule j.val).support, |rule j.val u| *
        (cost M j * (ε + response G κ b g (2*M+1) u * t^(2*M+1))) := by
  intro X κ
  let A := Tensor.coeff (original H (N:=N) φ g) j.val 0
  let B := Tensor.coeff (reading p g T) j.val 0
  let K := A-B
  have phys := WilsonPosteriorProjectionGerm.regular H sel hm φ g j.val funded hb
  have aSym : Tensor.Sym A := Tensor.coeff_symm phys
  have bSym : Tensor.Sym B := Tensor.coeff_symm (WilsonPosteriorProjectionBank.regular p g T j.val).contDiffAt
  have sym : Tensor.Sym K := by
    intro y s
    simp only [K,sub_apply,aSym y s,bSym y s]
  have localPrice (u) (hu : u ∈ (rule j.val).support) :
      |K (fun _ => studio v u)*t^j.val| ≤ cost M j*(ε+response G κ b g (2*M+1) u*t^(2*M+1)) := by
    let Z := studio v u
    have vals (i : J M) : |ray (posterior H (N:=N) φ) g Z (t*probe M i) -
        ∑ k : J M, component p g T Z k.val * (t*probe M i)^k.val| ≤ ε := by
      rw [← clock p M g T degree Z]
      exact samples u hu i
    have paid := WilsonPosteriorProjectionMeasured.row_price H sel hm φ g Z M
      (fun k => component p g T Z k.val) j t ε ht funded hb vals
    have same : K (fun _ => Z) =
        row (ray (posterior H (N:=N) φ) g Z) j.val-component p g T Z j.val := by
      change Tensor.diagonal A Z - Tensor.diagonal B Z = _
      rw [on_ray H φ g j.val Z phys,WilsonPosteriorProjectionBank.diagonal p M g T degree Z j]
    rw [show K (fun _ => studio v u) = _ from same]
    apply paid.trans
    apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun i _ => abs_nonneg _)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht.le _)
    have tf : 0≤tariff G := zero_le_one.trans (fee G)
    have field : 0 ≤ 1+(abs κ)*tariff G := by positivity
    have dir : 0 ≤ ∑ i, ‖direction g Z i‖ := sum_nonneg fun i _ => norm_nonneg _
    have e0 : 0 ≤ bill H (fun i => ‖direction g Z i‖) N (m+1) :=
      mul_nonneg field (by positivity)
    have bound : bill H (fun i => ‖direction g Z i‖) N (m+1) ≤
        (1+(abs κ)*tariff G)*(1+(abs g)*slots u) := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (studio_toll v u g)) field
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg e0 _)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ e0 bound _) (abs_nonneg _))
  change |K X*t^j.val| ≤ _
  rw [show K X = _ from wire_component v K sym,sum_mul]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro u hu
  rw [mul_assoc,abs_mul]
  exact mul_le_mul_of_nonneg_left (localPrice u hu) (abs_nonneg _)

end YM.Integration.WilsonPosteriorProjectionCoefficient

