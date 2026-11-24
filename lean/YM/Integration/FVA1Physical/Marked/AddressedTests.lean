import YM.Integration.FVA1Physical.Marked.StencilTests
import YM.Integration.LocalComparisonInterface

/-! Independent physical position tests at every marked slot. Each row can
read a prescribed derivative, position and tuple of directions. The common
weighted test envelope is retained before evaluating any stencil. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open ComparisonDensity.Address LocalComparison Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern
open scoped BigOperators Classical

/-- The location and derivative of a test function used at one stencil row.
All positions, directions and weights are fixed before a test is chosen. -/
structure JetProbe (D : Orbit) where
  order : ℕ
  withinOrder : order ≤ D.D
  point : Pos
  inScope : point ∈ D.scope
  directions : Fin order → Pos
  unitDirections : ∀ j, ‖directions j‖ ≤ 1

namespace JetProbe
variable {D : Orbit}

def evaluation (p : JetProbe D) (f : Pos → ℂ) : ℂ :=
  iteratedFDeriv ℝ p.order f p.point p.directions / (D.height p.point : ℂ)

theorem evaluation_norm (p : JetProbe D) (f : Pos → ℂ) (h : D.Bill f 1) :
    ‖p.evaluation f‖ ≤ 1 := by
  unfold evaluation
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (D.sky _).le]
  apply (div_le_one (D.sky _)).mpr
  apply ((iteratedFDeriv ℝ p.order f p.point).le_opNorm p.directions).trans
  refine (mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => p.unitDirections i))).trans ?_
  simpa using h.limits _ p.withinOrder _ p.inScope

/-- A complex test uses the two real components of its actual normalized jet. -/
def component (p : JetProbe D) (imag : Bool) (f : {f : Pos → ℂ // D.Bill f 1}) :
    Set.Icc (-1 : ℝ) 1 :=
  ⟨if imag then (p.evaluation f.val).im else (p.evaluation f.val).re,
    abs_le.mp (by split
                  · exact (Complex.abs_im_le_norm _).trans (p.evaluation_norm _ f.property)
                  · exact (Complex.abs_re_le_norm _).trans (p.evaluation_norm _ f.property))⟩

theorem complex_components (p : JetProbe D) (f : {f : Pos → ℂ // D.Bill f 1}) :
    (((p.component false f : ℝ) : ℂ) + ((p.component true f : ℝ) : ℂ) * Complex.I)
      = p.evaluation f.val := Complex.re_add_im _
end JetProbe

variable {V : Type} [DecidableEq V] {B : Census V} {ξ : V → ℕ} {qd : ℕ}

/-- A separate marked address at each source, perturbative order, derivative rank
and countable summand. The real and imaginary projections may be chosen separately
for each slot. -/
abbrev RowAddresses (D : V → Orbit) (B : Census V) (ξ : V → ℕ) (qd : ℕ) :=
  ∀ (v : V) (s : Senses B) (e : Fin (qd+1)),
    Fin (e.val+Lagger.dues ξ s.val+1) → ℕ → JetProbe (D v)

def fromAddressedTests (D : V → Orbit) (atRow : RowAddresses D B ξ qd)
    (imag : V → Bool) (f : IndependentTests D) : V → StencilTests B ξ qd :=
  fun v s e n j => (atRow v s e n j).component (imag v) (f v)

/-- All real/imaginary components of independent polynomially weighted
position tests have the same paid analytic stencil envelope. -/
theorem addressed_stencil_allows {G : Gauge} (D : V → Orbit)
    (atRow : RowAddresses D B ξ qd) (imag : V → Bool) (f : IndependentTests D)
    (A : Stanza B G ξ qd) {b : ℕ} {a C : ℝ}
    (h : (Stanza.son A b).Allows a C) :
    (Stanza.son (testedStencil A (slotTests (fromAddressedTests D atRow imag f))) b).Allows a C :=
  testedStencil_allows _ _ h

end YM.Integration.FVA1Physical.Marked
