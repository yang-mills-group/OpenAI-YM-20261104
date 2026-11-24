import YM.FullVolume.Roll.Divide
import YM.Extension.UV.Canon.Core

/-! Retain the original kinetic data at the very directed factor issued by
the physical sale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowArchive
open Function Filter Set Lattice Wilson Pressure RG RG.Supply RG.Shoot Input Precision Org
open Push.PriceCompiler Push.SectorMeasure AnalyticBridge.VerifiedReset
open PhysicalNext ThroughLaunch Repeat WilsonStartup Extra.Histories Next.Scheduling
open Next.Foundations UVNext.CouplingReset Progress.DirectedRecipe Further.StrongStartup

/-- The two older horizons, the stationary field and their overlay are the
ones in this physical purchase. The startup invoice gives the permissions at
every cutoff of the same levels. -/
theorem archive_of_imperial {G : Gauge} (hG : G.Simple) {s : Sheet G} {l : ℕ → ℕ}
    {D : Rolls (ThroughLaunch.raise s l)} {P : PostCost D} {θ : Protection D}
    {V : Delays θ} {b : Bar V} {I : Wait b} {a : Levels G} {M : Horizon a}
    {k : Kin M (chart G)} {O T : MapPrices} {u : ℕ → ℝ} {t : Tariffs}
    (bought : ThroughLaunch.Imperial O T u P a M k) (ha : Paid I a)
    (hx : Prices (ThroughLaunch.raise s l) t (localSection G) V.betaEntry) {E F} :
    Extension.UV.Archive
      (Progress.DirectedRecipe.prepared k E F (permissions a) ha bought.finalMap
        (chart_ok _) bought.paths) where
  kinetic := by
    obtain ⟨X, W, v, h⟩ := bought.layer
    exact ⟨X, W, v, O, T, u, h⟩
  top := bought.top
  startup := fun N => (spending hG ha hx N).1.old

end YM.Integration.WilsonWindowArchive
end

