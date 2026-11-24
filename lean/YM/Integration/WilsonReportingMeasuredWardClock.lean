import YM.Integration.WilsonMatrixOriginalGermForecast
import YM.Integration.WilsonReportingMeasuredWardProgram

/-! The fixed source gets its unit from the true reporting regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardClock
open Filter Lattice Wilson RG RG17 Spec Extraction Source
open PhysicalNext.Repeat.Legato Trace.Physical Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentLimit
open scoped Classical BigOperators Topology

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} (L:Layout F) (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ)) ≤ L.lens)
    (τ:ℕ→ℝ) (climate:Climate R U τ)

def unit (R:Run G) (τ:ℕ→ℝ) (m:ℕ):ℝ:=τ m*R.family.path.levels.clock.threshold m
def gain (R:Run G) (τ:ℕ→ℝ) (m:ℕ):ℝ:=(unit R τ m^2)⁻¹

include climate in
theorem realized (m:ℕ):0<unit R τ m ∧
    Tendsto (fun z:ℕ×ℕ=>Pert.Asymptotics.regulatorRun R.family z.1 z.2 m)
      (U:Filter _) (𝓝 (unit R τ m)):=by
  let θ:=R.family.path.levels.clock.threshold m
  have hp:0<θ:=(R.family.path.levels.budget m).threshold_pos
  refine ⟨mul_pos (climate m).1 hp,?_⟩
  have un (z:ℕ×ℕ):shrink R.family m z.1 z.2*θ=Pert.Asymptotics.regulatorRun R.family z.1 z.2 m:=
    div_mul_cancel₀ _ hp.ne'
  exact ((climate m).2.2.mul_const θ).congr un

include cut climate in
theorem original (m:ℕ):
    0<gain R τ m ∧ gain R τ m ≤ 2*R.family.path.levels.clock.hatBeta m ∧
    Tendsto (fun z:ℕ×ℕ=>Pert.Asymptotics.regulatorRun R.family z.1 z.2 m^2*gain R τ m)
      (U:Filter _) (𝓝 1) :=by
  obtain ⟨hp,lim⟩:=realized U τ climate m
  have up:∀ᶠz:ℕ×ℕ in (U:Filter _),m ≤ z.1:=
    ((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono (cut.trans L.certified)
  have positive:0<gain R τ m:=inv_pos.mpr (sq_pos_of_pos hp)
  refine ⟨positive,?_,?_⟩
  · have fare: Tendsto (fun z:ℕ×ℕ=>(Pert.Asymptotics.regulatorRun R.family z.1 z.2 m^2)⁻¹)
        (U:Filter _) (𝓝 (gain R τ m)):=(lim.pow 2).inv₀ (pow_ne_zero _ hp.ne')
    apply le_of_tendsto fare
    filter_upwards [up] with z zm
    have rep:=(R.makes.wilson.represents z.1 z.2 m zm).band
    have hot:0≤R.family.path.β z.1 z.2 m:=(div_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed m).le) (by norm_num:0≤(2:ℝ))).trans rep.1
    change (((Real.sqrt (R.family.path.β z.1 z.2 m))⁻¹)^2)⁻¹≤_
    rw [inv_pow,inv_inv,Real.sq_sqrt hot]
    exact rep.2
  · have limit: (unit R τ m)^2*gain R τ m=1:=mul_inv_cancel₀ (pow_ne_zero _ hp.ne')
    exact limit ▸ (lim.pow 2).mul_const (gain R τ m)

end YM.Integration.WilsonReportingMeasuredWardClock
