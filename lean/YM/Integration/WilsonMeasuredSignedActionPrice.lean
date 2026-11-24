import YM.Integration.WilsonMeasuredSignedActionVote
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionPrice
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Extraction Push.RelayDifference Bandage
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionVote
open WilsonMeasuredSignedActionAverage WilsonMeasuredSignedActionDebits
open WilsonMaxwellThermometerStationHeads WilsonPhysicalChiralNonfreeStationMoney
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "F₀" => R.family.labels.level 4
local notation "C₀" => R.family

theorem period (j:ℕ)(f:Extraction.Order):
    Tendsto (fun z:Cutoffs=>rent R j z.2) f.fuse (𝓝 0):=by
  have price:=WilsonPhysicalChiralNonfreeStationMoney.period R 4 j f
  have small:Tendsto (fun z:Cutoffs=>max 0 (levy R 4 z.1 z.2 j)) f.fuse (𝓝 0):=by
    simpa only [max_self] using (tendsto_const_nhds (x:=(0:ℝ))).max price
  apply small.congr'
  filter_upwards [(cutoff_grows f).eventually_ge_atTop j] with z late
  unfold WilsonMeasuredSignedActionVote.rent levy
  have same:(R.family.path.rep z.1 z.2 j).p=plank C₀ j:=(R.makes.wilson.represents z.1 z.2 j late).vac
  rw [same]
  rfl

def fare (j:ℕ)(z:Cutoffs)(W:ℝ):ℝ:=((fee R j+|levy R 4 z.1 z.2 j|)/(1-fee R j))*W

theorem original (simple:G.Simple)(f:Extraction.Order)(W:ℝ)
    (nz:0<(F₀).coeffSize (axis F₀)):
    ∀ᶠ j:ℕ in atTop,∀ᶠ z:Cutoffs in f.fuse,
      cost F₀*((fare R j z W+rent R j z.2*(F₀).coeffSize (axis F₀))/(1-rent R j z.2))<
        total*(F₀).coeffSize (axis F₀):=by
  let a:=(F₀).coeffSize (axis F₀)
  have income:Tendsto (fun j:ℕ=>fee R j) atTop (𝓝 0):=rate R simple
  have elapsed:Tendsto (fun j:ℕ=>fee R j/(1-fee R j)) atTop (𝓝 0):=by
    have h:ContinuousAt (fun x:ℝ=>x/(1-x)) 0:=
      continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    simpa only [Function.comp_def,zero_div] using h.tendsto.comp income
  have small:Tendsto (fun j:ℕ=>cost F₀*(fee R j/(1-fee R j)*W)) atTop (𝓝 0):=by
    simpa using (elapsed.mul_const W).const_mul (cost F₀)
  have credit:0<total*a:=mul_pos total_pos nz
  filter_upwards [small.eventually (gt_mem_nhds credit),income.eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1))] with j bought decent
  have lev:= (WilsonPhysicalChiralNonfreeStationMoney.period R 4 j f).abs
  have fares:Tendsto (fun z:Cutoffs=>fare R j z W) f.fuse (𝓝 (fee R j/(1-fee R j)*W)):=by
    simpa only [fare,abs_zero,add_zero] using (((tendsto_const_nhds (x:=fee R j)).add lev).div_const (1-fee R j)).mul_const W
  have wind:=period R j f
  have rev:Tendsto (fun z:Cutoffs=>cost F₀*((fare R j z W+rent R j z.2*a)/(1-rent R j z.2))) f.fuse
      (𝓝 (cost F₀*(fee R j/(1-fee R j)*W))):=by
    simpa using ((fares.add (wind.mul_const a)).div (tendsto_const_nhds.sub wind) (by norm_num:(1:ℝ)-0≠0)).const_mul (cost F₀)
  exact rev.eventually (gt_mem_nhds bought)
end YM.Integration.WilsonMeasuredSignedActionPrice
end
