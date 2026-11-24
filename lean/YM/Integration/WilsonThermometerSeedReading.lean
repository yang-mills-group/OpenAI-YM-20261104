import YM.Integration.WilsonThermometerDeclaredSeeds
import YM.Integration.SignedMarkedChartGerm

/-! Read the independently declared real projection at its true nonlinear
periodic link field before any conditional Gaussian substitution. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSeedReading
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonCoeffUV.Bank WilsonCoeffUV.Fountain WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Soil
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} (d : V→ℕ)
  (g τ : ℝ) (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)
  {D : V→ℕ} (knob : (j:V)→Knob (D j)) (p : V→Chamber)
  (L : ℂ→L[ℝ]ℝ) (x:T)
local notation "B" => bank R d g τ v t knob p L x

theorem native (i : Entry R d) (u : Fin (rank R d i)→G.Color) :
    ↑((raw R d i).poly u) = NativeCurvatureTensor.value (key R d i) u := by
  rw [RG.Atom.poly,NativeCurvatureTensor.value,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.ofReal_mul,color R d]
  push_cast
  ring

theorem actual {n : Side} (j : V) (b : Choice R d j) (U : Config G n) (z : Site n) :
    (colour (B j b).path (B j b).color (B j b).weight (B j b).quadrant).unmasked U z =
      L (t j x*scalar R d g τ v (entry R d j b)*↑((raw R d (entry R d j b)).unmasked U z)) := by
  unfold RG.Atom.unmasked
  rw [colour_poly]
  change L (_*NativeCurvatureTensor.value (key R d (entry R d j b))
    (fun l=>((raw R d (entry R d j b)).leg l).atSite U z)) = _
  rw [←native R d (entry R d j b)]
  rfl

/-- Recover the whole genuine complex source at a copied site from its two
independent real projections on exactly the same field. -/
theorem held {n : Side} (j : V) (b : Choice R d j) (s : ℝ) (U : Config G n) (z : Site n) :
    let i := entry R d j b
    L (WilsonThermometerFrozenCopies.word R d g τ v t i s x z U) =
      s^(d j+1-pole R d i)*(colour (B j b).path (B j b).color (B j b).weight (B j b).quadrant).unmasked U z := by
  dsimp only
  rw [actual R d g τ v t knob p L x]
  unfold WilsonThermometerFrozenCopies.word
  rw [site,WilsonThermometerFrozenSockets.separated R d g τ v]
  simp only [Complex.ofReal_mul]
  rw [←smul_eq_mul (s^(d j+1-pole R d (entry R d j b))),←map_smul]
  congr 1
  change _ = (↑(s^(d j+1-pole R d (entry R d j b))):ℂ)*_
  ring

end YM.Integration.WilsonThermometerSeedReading
