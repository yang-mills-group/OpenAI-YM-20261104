import YM.Comparison.RG02.Thermal.Kept
import YM.Comparison.RG02.Symmetry.Code
import YM.Integration.RunFormalChain
import YM.FVAAlt2.Boot.Start

/-! The manuscript's negative conditional logarithm, evaluated directly on
the finite integral. No positive-action extension or selected Plan is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioSignedReading

open Function Filter Matrix Lattice Tree Wilson RG Precision Exterior Marker
open Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Bulk
open Comparison.RG02.Thermal Order Next.SectorChange Integral
open PhysicalNext.Repeat.Legato Integration.RunFormalChain RegulatorIR.FVAAlt2
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {R : Census I}
    {P : History G} (Y : Bulk.Chain P) (N m p : ℕ) (hm : m < N)
    (F : Forest (P.levels.clock.op m p).ratio) (u : (P.levels.clock.op m p).Choices)
    (W : Bulk.Colors R G (P.S.side (m+1) p)) (r : ℕ)

def action (B : fieldDir G (P.S.side m p) 1) : ℝ :=
  -(Symmetry.Orbit.ground (Y.step N m p hm) F u W r 2 B -
    Symmetry.Orbit.ground (Y.step N m p hm) F u W r 2 0).re

def primitive (B : fieldDir G (P.S.side m p) 1) : ℝ :=
  mainTerm (P.rep N p m).clip (P.rep N p m).path (represent B)

def fluctuation : fieldDir G (P.S.side m p) 1 → ℝ :=
  Precision.thermal F u (P.rep N p (m+1)).clip (P.rep N p (m+1)).path
    ((Y.step N m p hm).b F) Y.O

/-- The signed logarithm's quartic primitive and its quadratic fluctuation,
with all open color directions and the original integration still present. -/
theorem response (hW : W.Standard) (hr : 2 ≤ r) (B : fieldDir G (P.S.side m p) 1) :
    action Y N m p hm F u W r B =
      jet (primitive (P := P) N m p) 4 B +
        jet (fluctuation Y N m p hm F u) 2 B := by
  have h : action Y N m p hm F u W r B = Thermal.Layers.forecast
      (Y.step N m p hm) F u B 2 := by
    have hw := Thermal.Wick.sq (Y.step N m p hm) F u W hW B hr
    unfold action Symmetry.Orbit.ground
    simp only [if_neg (by decide : (2:ℕ) ≠ 0), add_zero]
    change -(Order.Second.lit 2 (logVac (Fk (Y.step N m p hm) F u W B r)) -
      Order.Second.lit 2 (logVac (Fk (Y.step N m p hm) F u W 0 r))).re = _
    rw [hw, add_sub_cancel_right, Complex.neg_re, Complex.ofReal_re, neg_neg]
  rw [h, Thermal.Layers.forecast, Thermal.keeps_class Y N m p hm F u 4 (by decide)]
  rfl

def quadratic (B : fieldDir G (P.S.side m p) 1) : ℝ :=
  (16 * action Y N m p hm F u W r B -
    action Y N m p hm F u W r ((2:ℝ) • B)) / 12

/-- A finite pair of genuine observations extracts the exact squared-field
coefficient, retaining the thermal covariance of this specific torus. -/
theorem measured (hW : W.Standard) (hr : 2 ≤ r) (B : fieldDir G (P.S.side m p) 1) :
    quadratic Y N m p hm F u W r B = jet (fluctuation Y N m p hm F u) 2 B := by
  unfold quadratic
  rw [response Y N m p hm F u W r hW hr B,
    response Y N m p hm F u W r hW hr ((2:ℝ) • B), Clipper.weight B (2:ℝ) 4,
    Clipper.weight B (2:ℝ) 2]
  simp only [smul_eq_mul]
  ring

/-- The finite signed measurements read the genuine finite thermal price
on the same incoming waves as the stationary kinetic theorem. -/
theorem wave (hW : W.Standard) (hr : 2 ≤ r) (i j : Site (P.S.side m p))
    (σ τ : TypeFace 1 → G.ColorIndex → ℂ)
    (hσ : ∀ x y, ‖σ x y‖ ≤ 1) (hτ : ∀ x y, ‖τ x y‖ ≤ 1) :
    let Z := ![Precision.wave i σ, Precision.wave j τ]
    |iteratedFDeriv ℝ 2 (quadratic Y N m p hm F u W r) 0 Z -
      iteratedFDeriv ℝ 2 (draft (Y.kin.alpha N m) (P.rep N p m).path
        (P.rep N p m).clip) 0 Z| ≤ (Fintype.card (Site (P.S.side m p)) : ℝ) *
          Y.post.Γ (P.levels.clock.J (m+1)) * P.levels.clock.loopCap (m+1) *
          Real.exp (-(Y.post.c (P.levels.clock.J (m+1))) * (P.S.side m p).val) := by
  have hread : quadratic Y N m p hm F u W r = jet (fluctuation Y N m p hm F u) 2 :=
    funext (measured Y N m p hm F u W r hW hr)
  have ht : ContDiffAt ℝ ω (fluctuation Y N m p hm F u) 0 :=
    (Thermal.retained Y N m p hm).born u
  rw [hread, Thermal.re_jet ht 2 2, if_pos rfl]
  simpa only [fluctuation] using
    (Thermal.retained Y N m p hm).wave_price u i j σ τ hσ hτ

/-- The true marked bare Wilson field supplies the input regularity itself. -/
theorem opening {d : ℕ} (T : Run G) (E : Census I) (i : I) (b : Boot.Scout (G:=G) d)
    (m p : ℕ) (F : Forest (T.family.path.levels.clock.op m p).ratio)
    (u : (T.family.path.levels.clock.op m p).Choices) (r : ℕ) (hr : 2 ≤ r)
    (B : fieldDir G (T.family.side m p) 1) :
    quadratic (fromRun T) (m+1) m p (Nat.lt_succ_self m) F u
      (Boot.ink E i T.family.path (m+1) p b) r B =
        jet (fluctuation (fromRun T) (m+1) m p (Nat.lt_succ_self m) F u) 2 B :=
  measured _ _ _ _ _ _ _ _ r (Boot.authentic E i T.family.path (fromRun T) (m+1) p b) hr B

end YM.Integration.MSFixedRatioSignedReading
end
