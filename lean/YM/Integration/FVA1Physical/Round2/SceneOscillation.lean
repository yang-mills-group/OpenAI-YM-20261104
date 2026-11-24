import YM.Integration.FVA1Physical.Wilson.CylinderOscillation
import YM.Integration.FVA1Physical.Round2.AllSceneVacuum

/-! Oscillation of the discrepancy between the physical incoming action and the independently
iterated Wilson action on a finite patch. Exterior links can be arbitrarily nonflat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Pressure
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)

/-- The physical and independently rebuilt Wilson weights have a volume-independent
relative log price on every bounded-displacement incoming chart, at every RG depth. -/
theorem allscene_patch_oscillation (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∀ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S →
      ∀ j, k ≤ j → ∀ hj : j ≤ N, ∀ (T : Slices C.path.levels n)
        (h : (traversal T hj).Room G) (tag : (traversal T hj).Tags)
        (x v : Positions (Primary (C.side j n) G)),
        let g := Heath.Stock.cue (C.path.rep N n j).beta
        let w := Mosaic.vol (C.path.levels.clock.hatBeta j)
        let E := sceneVacuumError L S T hj h tag p g
        (∀ t ∈ Set.Icc (0:ℝ) 1, x+t • v ∈ Metric.closedBall 0 w) →
        |E (x+v)-E x| ≤ (∑ i, |v i|) * (g^((p:ℝ)+1-η)/w) := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [Round2.allscene_vacuum_envelope simple sel D s p m 0 hs hm hp (by omega) hη,
    D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀] with k bought purse cutoff
  intro N n lo S hS
  have rows := (bought N n lo S hS).1
  have checks := ((purse N n lo).2 S hS).1
  intro j hk hj T h tag x v g w E inside
  let Q := C.path.rep N n j
  have wide := h₀ j (cutoff.trans hk)
  have J := rows j hk hj
  dsimp only at J
  rw [sceneVacuumError_eq L S T hj h tag hS hk (Nat.le_succ p)] at J
  apply patch_oscillation J (div_pos wide (by norm_num))
    (zpow_nonneg wide.le _) _ x v inside
  intro y hy
  change DifferentiableAt ℝ (sceneVacuumError L S T hj h tag p g) y
  rw [←sceneVacuumError_eq L S T hj h tag hS hk (Nat.le_succ p)]
  have top : ContDiffAt ℝ (2:ℕ) (Aqua.film Q (S.Poly j) g (p+1)) y :=
    ((checks j hk hj).grown y hy).of_le (by exact_mod_cast (show 2 ≤ m+1 by omega))
  have pure (i) := (Aqua.pure Q (S.Poly j) g i).contDiffAt (x:=y)
  have actual : ContDiffAt ℝ (2:ℕ) (Aqua.vine Q g) y := by
    have all := top.add ((pure (p+1)).of_le le_top)
    convert all using 1
    funext z;change Aqua.vine Q g z=(Aqua.vine Q g z-_) + _;abel
  exact (actual.sub ((pure p).of_le le_top)).differentiableAt (by simp)

end YM.Integration.FVA1Physical.Wilson

