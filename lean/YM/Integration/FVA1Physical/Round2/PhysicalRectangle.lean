import YM.Integration.FVA1Physical.Round2.SceneOscillation
import YM.Integration.FVA1Physical.Round2.RectangleLedger

/-! Volume-independent spatial summability of finite mixed-coordinate changes of
the non-bare log discrepancy against the prescribed independent Wilson history.
Each tuple is allowed its own held derivatives, weak background and changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Pressure
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato Integration.FVA1Physical.Wilson
open scoped Classical Topology ContDiff

theorem RectangleLedger.spend {σ : Type} [Fintype σ] {n : Side} {site : σ → Site n} {a w B : ℝ}
    {s m : ℕ} {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (H : RectangleLedger site a s w S F m B) (i : σ)
    (r : List σ → ℕ) (h : List σ → σ → ℝ) (x : List σ → Positions σ)
    (cap : ∀ l : List σ, l.length=m → ∀ j, |h l j| ≤ w)
    (inside : ∀ l : List σ, l.length=m →
      rectangleInside (h l) S ((i::l).take (r l)).reverse (x l)) :
    Yarn m (fun l : List σ=>
      |mixedRectangle F (i::l) (r l) (h l) (x l)| * w^((i::l).drop (r l)).length *
      Measuring.swipe site a s (i::l)) ≤ B := by
  obtain ⟨price,paid,row⟩ := H.covers
  apply (shiny m _).trans (row i)
  intro l hl
  exact mul_le_mul_of_nonneg_right ((paid (i::l) (by simp [hl])).2 (r l) (h l) (x l) (cap l hl) (inside l hl))
    (effect site a s ∅ (i::l)).le

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)

theorem allscene_rectangles (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m q : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) (hq : q+1 ≤ m) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∀ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S →
      ∀ j, k ≤ j → ∀ hj : j ≤ N, ∀ (T : Slices C.path.levels n)
        (h : (traversal T hj).Room G) (t : (traversal T hj).Tags),
        let β := C.path.levels.clock.hatBeta j
        let w := Mosaic.vol β
        let g := Heath.Stock.cue (C.path.rep N n j).beta
        RectangleLedger (Measuring.chart _ G) (Mosaic.αm β) s w (Metric.closedBall 0 w)
          (sceneVacuumError L S T hj h t p g) q (g^((p:ℝ)+1-η)) := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [allscene_vacuum_envelope simple sel D s p m q hs hm hp hq hη,
    D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀] with k env purse cut
  intro N n lo S hS j hj top T h t β w g
  let Q := C.path.rep N n j
  have J := (env N n lo S hS).1 j hj top
  dsimp only at J
  rw [sceneVacuumError_eq L S T top h t hS hj (Nat.le_succ p)] at J
  have wide := h₀ j (cut.trans hj)
  apply rectangle_ledger J (div_pos wide (by norm_num)) (k:=m+1) _ (by omega)
  intro y hy
  rw [←sceneVacuumError_eq L S T top h t hS hj (Nat.le_succ p)]
  have H := ((((purse N n lo).2 S hS).1 j hj top).grown y hy)
  have poly (b : ℕ) := (Aqua.pure Q (S.Poly j) g b).contDiffAt (x:=y)
  have source : ContDiffAt ℝ (m+1:ℕ) (Aqua.vine Q g) y := by
    have tot := H.add ((poly (p+1)).of_le le_top)
    convert tot using 1
    funext z; change Aqua.vine Q g z = (Aqua.vine Q g z - _) + _; abel
  exact source.sub ((poly p).of_le le_top)

end YM.Integration.FVA1Physical.Round2
