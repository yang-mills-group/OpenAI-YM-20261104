import YM.Gauge.Casimir

/-! The colour and open-index part of the candidate ghost self-energy residue,
and the finite correction produced by a regulated contracted complement. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Exchange.CalibratedExpansion.GhostPole

open scoped InnerProductSpace

private def color (G : Gauge) (a b : G.Color) : ℝ :=
  -LinearMap.trace ℝ G.Color (G.ad a * G.ad b)

def colorTrace (G : Gauge) : ℝ :=
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  ∑ i : G.ColorIndex, color G (b i) (b i)

def dot4 (p u : Fin 4 → ℝ) : ℝ :=
  p 0 * u 0 + p 1 * u 1 + p 2 * u 2 + p 3 * u 3

def curl12 (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![-p 1, p 0, 0, 0]

def openPole (G : Gauge) (a b : G.Color) (p v : Fin 4 → ℝ) : ℝ :=
  color G a b / (4 * Real.pi) ^ 2 *
    (dot4 p p * dot4 v v / 12 + (dot4 p v) ^ 2 / 6)

theorem original_ghost_transverse {G : Gauge} (h : G.Simple)
    (a b : G.Color) (p : Fin 4 → ℝ) :
    openPole G a b p (curl12 p) =
      G.casimir * ⟪a, b⟫_ℝ / (192 * Real.pi ^ 2) *
        dot4 p p * ((p 0) ^ 2 + (p 1) ^ 2) := by
  have ortho : dot4 p (curl12 p) = 0 := by
    simp [dot4, curl12]
    ring
  have square : dot4 (curl12 p) (curl12 p) = (p 0) ^ 2 + (p 1) ^ 2 := by
    simp [dot4, curl12]
    ring
  rw [openPole, color, Gauge.trace_adjoint h, ortho, square]
  field_simp [Real.pi_ne_zero]
  ring

theorem original_ghost_trace {G : Gauge} (h : G.Simple) :
    colorTrace G = (G.lieDim : ℝ) * G.casimir := by
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  have row (i : G.ColorIndex) : color G (b i) (b i) = G.casimir := by
    rw [color, Gauge.trace_adjoint h, b.inner_eq_one, mul_one]
  change (∑ i : G.ColorIndex, color G (b i) (b i)) = _
  simp [row, nsmul_eq_mul]

def separatedPin (G : Gauge) : ℝ :=
  colorTrace G / (192 * Real.pi ^ 2) * (1 / Real.pi ^ 2) ^ 2

theorem original_separated_pin_pos {G : Gauge} (h : G.Simple) : 0 < separatedPin G := by
  haveI := h.nontrivial_color
  have hd : 0 < G.lieDim := by
    rw [Gauge.lieDim, ← G.colorIso.finrank_eq]
    exact Module.finrank_pos
  have hp := Gauge.casimir_pos h
  rw [separatedPin, original_ghost_trace h]
  positivity

theorem original_ghost_finite_quotient (G : Gauge) {z : ℝ} (hz : z ≠ 0)
    (q₀ q₁ : ℝ) :
    separatedPin G / z * (q₀ + z * q₁) - separatedPin G / z * q₀ =
      separatedPin G * q₁ := by
  field_simp [hz]
  ring

end YM.Integration.FVA1Physical.Exchange.CalibratedExpansion.GhostPole
