import YM.Integration.FVA1Physical.Wilson.InheritedPatch
import YM.MSbar.Cottage.Copy

/-! Localize the independent Wilson bank at a genuinely non-bare scale. The true
input and its anchor may have failed plaquettes outside a local healthy collar.
The forced gas is kept at its exact value in the true configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {f : Side}

theorem log_eval (R : Rep G f) (positive : ∀ U, 0 < R.eval U) (U : Config G f) :
    Real.log (R.eval U) = R.exponent U + Real.log (R.activities.gas R.p U) := by
  have pos : R.activities.gas R.p U ≠ 0 := by
    intro h
    have zero : R.eval U = 0 := by simp only [Rep.eval,h,mul_zero]
    exact (positive U).ne' zero
  rw [Rep.eval,Real.log_mul (Real.exp_pos _).ne' pos,Real.log_exp]

/-- Exact original gas, along with its explicit chart-copy correction. This permits
arbitrary exterior failures and even works when the copied gas itself is nonunit. -/
def copyCorrection (R : Rep G f) (U V U' V' : Config G f) : ℝ :=
  Real.log (R.activities.gas R.p U)-Real.log (R.activities.gas R.p V)-
    (Real.log (R.activities.gas R.p U')-Real.log (R.activities.gas R.p V'))

theorem copy_log_price (R : Rep G f) {σ C Λ δ w : ℝ} (paid : R.Lawful σ C Λ δ w)
    (pos : ∀ U, 0 < R.eval U) {Y : Support f} {d M : ℕ} (U V U' V' : Config G f)
    (original : Heath.Place Y M U U' V V' R.p.threshold)
    (charted : Heath.Place Y M U' U' V' V' R.p.threshold)
    (deep : Heath.Cottage.deepCopy R.p d ≤ M) (wide : R.p.B ≤ M)
    (dec : WilsonStartup.Decent R.clip R.p) (beta : 0 ≤ R.beta) :
    |(Real.log (R.eval U)-Real.log (R.eval V)) -
      (Real.log (R.eval U')-Real.log (R.eval V') + copyCorrection R U V U' V')| ≤
      Heath.Cottage.silkRoad C σ δ Λ R.beta Y.card M R.p d := by
  have bound := Heath.Cottage.copied paid original deep charted wide dec beta
  convert bound using 2
  simp only [log_eval R pos,copyCorrection]
  ring

variable {C : Family G} (L : Bulk.Chain C.path)

/-- On the actual path the independent coefficients for a wholly regular copy
price the local movement even when the actual exterior leaves the chart. The
second cost decays exponentially with the two independent localization radii.
Both costs are independent of the surrounding torus and specific fine fields. -/
theorem inherited_copied_bank (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j≤N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G)
        (tag : (traversal T hj).Tags) (Y : Support (C.side j n)) (d M : ℕ)
        (U V : Config G (C.side j n)) (x v : Positions (Primary (C.side j n) G)),
        let R := C.path.rep N n j
        let g := Heath.Stock.cue R.beta
        let w := Mosaic.vol (C.path.levels.clock.hatBeta j)
        let U' := palace (g • (x+v))
        let V' := palace (g • x)
        let B := boundaryBank L S T hj h tag p g
        let a := C.path.levels.params j
        let cal := C.path.levels.clock
        Heath.Place Y M U U' V V' R.p.threshold →
        Heath.Place Y M U' U' V' V' R.p.threshold →
        Heath.Cottage.deepCopy R.p d ≤ M → R.p.B ≤ M → WilsonStartup.Decent R.clip R.p →
        (∀ z∈Set.Icc (0:ℝ) 1, x+z • v ∈ Metric.closedBall 0 w) →
        |(Real.log (R.eval U)-Real.log (R.eval V)) -
          (B (x+v)-B x + copyCorrection R U V U' V')| ≤
          (∑ e,|v e|)*(g^((p:ℝ)+1-η)/w) +
          Heath.Cottage.silkRoad a.paths a.width (cal.allowance j) (cal.loopCap j) R.beta Y.card M R.p d := by
  filter_upwards [uniform_patch_oscillation L u simple sel D s p m hs hm hp hη] with k bought
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t Y d M U V x v R g w U' V' B a cal place copies deep wide decent circle
  have sell := sel.represents N n j hj
  have beta := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed j))).trans_le sell.band.1
  have exterior := copy_log_price R sell.good (SectorNext.Vacuum.strictly C.path sel N n j hj)
    U V U' V' place copies deep wide decent beta.le
  have inner := rows j hk hj T h t x v circle
  change |(Real.log (R.eval U')-B (x+v))-(Real.log (R.eval V')-B x)| ≤ _ at inner
  have eq : (Real.log (R.eval U)-Real.log (R.eval V)) -
      (B (x+v)-B x+copyCorrection R U V U' V') =
      ((Real.log (R.eval U')-B (x+v))-(Real.log (R.eval V')-B x)) +
      ((Real.log (R.eval U)-Real.log (R.eval V)) -
        (Real.log (R.eval U')-Real.log (R.eval V')+copyCorrection R U V U' V')) := by ring
  rw [eq]; exact (abs_add_le ..).trans (add_le_add inner exterior)

end YM.Integration.FVA1Physical.Wilson
