import YM.Integration.WilsonPosteriorProjectionHaar

/-! A signed homogeneous dependency of the genuine, normalized original
coarse posterior, measured against the independent polynomial at the same
points of the exponential ray. No previously matched derivative occurs as
an input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionMeasured
open Finset Set MeasureTheory Lattice Wilson RG Precision Tree Exterior Push.Uniform
open RG01.Kernel RG01.Kernel.Wheel LocalLTE.Weft
open WilsonPosteriorProjectionRay WilsonPosteriorProjectionTaylor
open WilsonPosteriorProjectionStencil WilsonPosteriorProjectionHaar
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable (φ : Config G (H.S.side (m+1) n) → ℝ) {b : ℝ}

include sel hm in
theorem row_price (g : ℝ) (z : Positions (Primary (H.S.side m n) G))
    (M : ℕ) (a : J M → ℝ) (j : J M) (t ε : ℝ) (ht : 0<t)
    (funded : Bounded (prior G (H.S.side (m+1) n))
      (fun (_ : (H.levels.clock.op m n).Choices) U => ((φ U : ℝ) : ℂ)) b)
    (hb : 0≤b) (samples : ∀ i : J M, |ray (posterior H (N:=N) φ) g z (t*probe M i) -
      ∑ k : J M, a k * (t*probe M i)^k.val| ≤ ε) :
    let q := 2*M+1
    let e := fun i => ‖direction g z i‖
    let B := bill H e N (m+1)^q * compensation G q (invoice q b) (1+2*1)
    |(row (ray (posterior H (N:=N) φ) g z) j.val-a j)*t^j.val| ≤
      cost M j * (ε + B*t^q) := by
  intro q e B
  let C := fun s : ℝ => conditional H N m n (represent (tint G _ (g • (s • z))))
    (fun _ U => ((φ U : ℝ) : ℂ))
  let R := ray (posterior H (N:=N) φ) g z
  have h := WilsonPosteriorProjectionConditional.measured H sel hm funded hb g z q
  have smoothC : ContDiff ℝ q C := h.1
  have comp : R = Complex.reCLM ∘ C := by
    funext s
    change _ = (conditional H N m n _ _).re
    rw [normalized H sel hm φ funded]
    rfl
  have smoothR : ContDiff ℝ q R := by
    rw [comp]
    exact Complex.reCLM.contDiff.comp smoothC
  have higher (s : ℝ) : ‖iteratedDeriv q R s‖ ≤ B := by
    have proj : iteratedDeriv q R s = (iteratedDeriv q C s).re := by
      rw [comp,iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_eq_iteratedFDeriv,
        Complex.reCLM.iteratedFDeriv_comp_left smoothC.contDiffAt le_rfl]
      rfl
    rw [proj,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (h.2 s)
  exact projected (posterior H (N:=N) φ) g z M a j t ε B ht smoothR
    ((norm_nonneg _).trans (higher 0))
    (fun s _ => (derivative (posterior H (N:=N) φ) g z q s) ▸ higher s) samples

end YM.Integration.WilsonPosteriorProjectionMeasured

