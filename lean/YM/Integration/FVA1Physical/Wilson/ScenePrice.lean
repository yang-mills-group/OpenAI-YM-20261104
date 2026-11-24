import YM.Integration.FVA1Physical.Wilson.SceneLedger
import YM.Integration.FVA1Physical.Round2.CalibratedEnvelope
import YM.Integration.FVA1Physical.Wilson.VolumeGeometry

/-! Rewrite the full volume-uniform vacuum derivative bound with the
independent Wilson ledger, at every retained scale and on its measured
coupling. This uses identities on the whole chart before differentiating. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function Finset RG Lattice YM.Wilson Exterior Tree Precision RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff

def chartPins (G : Gauge) (c : Side) (x : Positions (Primary c G)) : Pins G c :=
  fun i => tint G (Body 1 c) x (i.1,axisEquiv i.2)

theorem chartPins_recover {G : Gauge} {c : Side} (x : Positions (Primary c G)) :
    (tint G (Body 1 c)).symm (axesP G c (chartPins G c x)) = x := by
  apply (tint G (Body 1 c)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext1 i
  change tint G _ x (i.1,axisEquiv (axisEquiv.symm i.2)) = _
  rw [Equiv.apply_symm_apply]

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)
    {N n k r j : ℕ} (S : Scene C.path.levels n r) (T : Slices C.path.levels n)
    (hj : j ≤ N) (h : (traversal T hj).Room G) (t : (traversal T hj).Tags)

/-- The algebraically generated cutoff series in the measured chart. The
entire dependence on the chosen scene enters through its scalar coupling reset. -/
def sceneVacuumError (p : ℕ) (g : ℝ) (x : Positions (Primary (C.side j n) G)) : ℝ :=
  let u := chartPins G (C.side j n) x
  let A := variedVacuum (traversal T hj) L.O t h (formalSceneClock S N j) u
  Aqua.vine (C.path.rep N n j) g x -
    ∑ i ∈ range (p+1), g^i * Wave.bill (Real.log ∘ peval (term A) r) i

theorem sceneVacuumError_eq {v : G.Color} (hS : Realized L.kin N n k r v S) (hk : k ≤ j)
    {p : ℕ} (hp : p ≤ r) (g : ℝ) :
    Aqua.film (C.path.rep N n j) (S.Poly j) g p = sceneVacuumError L S T hj h t p g := by
  funext x
  apply congrArg (Aqua.vine (C.path.rep N n j) g x - ·)
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (g^i * ·)
  change Lis.atlas (S.Poly j) r i (C.path.rep N n j).path (C.path.rep N n j).clip x = _
  rw [L.selected N n j hj,L.clips N n j hj]
  have eqn := scene_ledger_coefficients S hS T hj hk h t L.receipt (chartPins G _ x)
    (show i ≤ r from (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hp)
  simpa only [chartPins_recover] using eqn

/-- Choose the cutoff before the initial scale, volume, forest, gauge tag,
positions, and held derivative directions. The true measured coupling, full
conditional vacuum and the complete weighted regular row use one scene. -/
theorem uniform_ledger_envelope (u : G.ColorIndex) (hg : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m q : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) (hq : q+1 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      (∀ j, k ≤ j → ∀ hj : j ≤ N, ∀ (T : Slices C.path.levels n)
        (h : (traversal T hj).Room G) (t : (traversal T hj).Tags),
        let Q := C.path.rep N n j
        let β := C.path.levels.clock.hatBeta j
        let V := Mosaic.vol β
        let g := Heath.Stock.cue Q.beta
        Lis.JetTab (Measuring.chart _ G) (Mosaic.αm β) s V (Metric.closedBall 0 V)
          (sceneVacuumError L S T hj h t p g) q (g^((p:ℝ)+1-η))) ∧
      ∀ j, k ≤ j → j < N →
        |Heath.Stock.cue (C.path.rep N n j).beta / Heath.Stock.cue (C.path.rep N n (j+1)).beta -
          Bakery.taste (p+1) (S.action j) (Heath.Stock.cue (C.path.rep N n j).beta)| ≤
          Mosaic.goalP (C.path.levels.clock.hatBeta j) (p+1) := by
  filter_upwards [Round2.calibrated_vacuum_envelope hg sel D s p m q hs hm hp hq hη] with k bought
  intro N n hN
  obtain ⟨S,hS,rows,reset⟩ := bought N n hN
  refine ⟨S,hS,?_,reset⟩
  intro j hk hj T h t
  dsimp only
  rw [← sceneVacuumError_eq L S T hj h t hS hk (Nat.le_succ p)]
  exact rows j hk hj

end YM.Integration.FVA1Physical.Wilson
