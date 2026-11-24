import YM.Integration.WilsonSeparatedOriginalSlabCubicInvoice
import YM.Integration.WilsonSeparatedOriginalSlabCubicPortfolio
import YM.Integration.WilsonSeparatedOriginalSlabChildCentered
import YM.Integration.WilsonSeparatedOriginalSlabChildPortfolio
import YM.Integration.WilsonSeparatedOriginalSlabChildRoom
import YM.Integration.WilsonReportHarvestSlabShiftSelected

/-! The actual signed nuclear cost is selected after the old date and the scale, once before all actual ultraviolet cutoffs and periods. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabUniform
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open WilsonAllDateHarvestFiledReplay WilsonAllDateHarvestHistoricalEntry WilsonAllDateHarvestNuclearProgram WilsonSeparatedOriginalSlabChildPortfolio
open RG05Readout.Nuclear RG05Readout.Pulse Push.GridApprox
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)(portfolio:Funding R)
variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
local notation "C"=>R.family
local notation "stopAt"=>WilsonMeasuredWindow.stop R.family.path.levels simple

def Settled (K d h b:ℕ)(s:Fin 3 → ℕ)(r η X cap:ℝ)(w:(i:Fin 3) → (C).label (s i))
    (hb:(C).ref 0 ≤ b)(nm:b+1 ≤ stopAt K r)(rank:ℕ)(g:Body)(σ:ℝ):Prop:=
  ∀ᶠt:ℕ in atTop,∃mt:stopAt K r ≤ t,∃nt:b+1<t,∀per:ℕ,
    WilsonSeparatedOriginalSlabChildRoom.Room C b ⌈cap+2⌉₊ r cap per →
    let H:=2*(h+1)+2*(K+1)
    let S:=fun i:Fin 3=>portfolio.basis (s i) (t+1,per)
    let x:=fun i:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s i) r (w i) (S i) (stopAt K r) (t+1) per
    ∃P:(i:Fin 3) → Sight C (s i) per, Registered R portfolio L s r w (b+1) (stopAt K r) (t+1) per d H P ∧
      ∃δ:ℝ,0 ≤ δ ∧ ∀Ψ:Wave (Fin 3),Scattering Ψ η → Tall Ψ (rank+1) 1 X →
        (∀y∈tsupport Ψ.val,∀i:Fin 3,‖y i‖ ≤ cap) → WilsonSeparatedOriginalSlabCubicPortfolio.Readout R nm mt nt s S P x hb Ψ rank r η X cap g δ σ

theorem purchased 
    (K d h b:ℕ)(s:Fin 3 → ℕ){r η X cap:ℝ}(w:(i:Fin 3) → (C).label (s i))(hb:(C).ref 0 ≤ b)(nm:b+1 ≤ stopAt K r)
    (rp:0<r)(room:r ≤ (C).S.a (b+1))(ep:0<η)(small:η ≤ 1)(rank:ℕ)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(xp:0 ≤ X)(cp:0 ≤ cap)
    (available:WilsonSeparatedOriginalSlabChildCentered.Bought R simple portfolio L K d h 0 b ⌈cap+2⌉₊ 1 η s r w nm)
    (g:Body){σ:ℝ}(target:0<σ):
    Settled R simple portfolio L K d h b s r η X cap w hb nm rank g σ:=by
  let B:=WilsonSeparatedOriginalProfileTariff.budget C s (b+1) rank r η X cap g
  let charge:=max 1 (B/σ)
  have one:1 ≤ charge:=le_max_left ..
  have pos:0<charge:=zero_lt_one.trans_le one
  have prices:B*(1/charge) ≤ σ:=by
    calc
      _=B/charge:=by ring
      _ ≤ σ:=(div_le_iff₀ pos).2 (by simpa only [mul_comm σ] using (div_le_iff₀ target).1 (le_max_right 1 (B/σ)))
  filter_upwards [available charge one] with t funded
  obtain ⟨mt,nt,rows⟩:=funded
  refine ⟨mt,nt,?_⟩;intro per enclosure
  obtain ⟨P,registered,paid⟩:=rows per
  let S:=fun i:Fin 3=>portfolio.basis (s i) (t+1,per)
  let x:=fun i:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s i) r (w i) (S i) (stopAt K r) (t+1) per
  refine ⟨P,registered,1/charge,one_div_nonneg.mpr pos.le,?_⟩;intro Ψ scatter sizeX shape
  obtain ⟨A,outside,heavy,cost⟩:=WilsonSeparatedOriginalSlabCubicPortfolio.purchased R nm mt nt s S P x hb
    (δ:=1/charge) (one_div_nonneg.mpr pos.le) rp room ep small Ψ rank grade scatter xp sizeX cp shape g
    (fun o ho c f sized sold=>by simpa [WilsonAllDateHarvestFixedSpectatorInvoice.extra] using paid o ho c enclosure.1 enclosure.2.1 f sized sold)
  exact ⟨A,outside,heavy,fun u=>(cost u).trans prices⟩

end YM.Integration.WilsonSeparatedOriginalSlabUniform
