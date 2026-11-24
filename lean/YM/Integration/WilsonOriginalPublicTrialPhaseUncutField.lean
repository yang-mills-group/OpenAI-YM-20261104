import YM.Integration.WilsonOriginalPublicTrialPhaseUncutCells
import YM.Integration.WilsonMeasuredPublicEntranceTransferSubmitted

/-! The genuinely fitted panel, all ordinary faces and every independently placed K site on the N prior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUncutField
open Function Finset Filter MeasureTheory Lattice Wilson RG Source Labels Cells OPE.Therm
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi Extra.Histories
open RG16 RG16.Literal RG05Readout RG05Readout.Many Push.GridApprox Push.Local
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMeasuredPublicEntranceTransferWord (field)
open WilsonMeasuredPublicEntranceTransferSubmitted (vector)
open scoped Topology Classical BigOperators
variable {G:Gauge}{n:ℕ}(R:Run G)
local notation "C" => R.family
local notation "S" => (C).S
local notation "A" => (C).path
local notation "H" i:arg => (A).levels.clock.hatBeta i

def Fee (u c q aperture pow:ℕ)(B:ℝ)(d:Fin n→ℕ)(s:Finset (Fin n)) : Prop:=
  ∀f K N per:ℕ,c≤f → ∀fk:f≤K,c+1<K → ∀live:K≤N,
    H K≤2*H c → (S).a c/(S).a K≤(H c)^aperture →
    ∀req age:ℕ,∀panel:Panel R d N per f K fk live req pow age B,
    ∀z:Fin n → Cover,(∀k∈s,‖(S).gridPoint K (z k)‖≤(S).a (c+1)/8) →
    ∀uk:u≤K,
    let M:=field (N:=N) R d (vector R d panel) (fun k=>wrap ((C).side K per) (z k)) s
    ‖(∫U,M U ∂scene (A) N per K)-actualTransport (C) (N:=N) M uk 1‖≤1/(H f)^q

set_option maxHeartbeats 1600000 in
theorem mask {T₀:Campaign R}(book:Campaign.Pillars R T₀)(simple:G.Simple)
    (purchase:RG05Preconstruction.ReadoutPurchase R.b)(storage:RG05Readout.Many.Storage (C) R.doors)
    (cater:Cater (C) R.doors)(tabs:Stock.Tabs (A).levels)(d:Fin n→ℕ)(s:Finset (Fin n))
    (j q aperture pow:ℕ)(B:ℝ)(non:0≤B)(ceiling:∀i,((A).levels.budget i).supportExponent=100):
    ∀ᶠ u:ℕ in atTop,∀ᶠ c:ℕ in atTop,Fee R u c q aperture pow B d s:=by
  classical
  by_cases has:s.Nonempty
  · obtain ⟨a,ha⟩:=has
    let h:=fun k:↥s=>d k.1
    have ready:=WilsonOriginalPublicTrialPhaseUncutCells.original R book simple purchase storage cater tabs h
      ⟨a,ha⟩ (fun _=>B) (fun _=>non) (fun _=>pow) j q aperture ceiling
    filter_upwards [ready] with u ready
    filter_upwards [ready] with c paid
    intro f K N per cf fk ck live heat optical req age panel z held uk
    obtain ⟨_,_,ear⟩:=paid f K N per cf fk ck live heat optical (fun k:↥s=>z k.1) (fun k=>held _ k.2)
      (fun k:↥s=>vector R d panel k.1) (fun k=>WilsonMeasuredPublicEntranceTransferSubmitted.wage R d panel k.1)
    intro M
    have same:M=WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) h
      (fun k:↥s=>wrap ((C).side K per) (z k.1)) (fun k:↥s=>vector R d panel k.1):=
        WilsonMeasuredPublicEntranceTransferSubmitted.density R d panel s _
    simpa only [same] using ear
  · rw [not_nonempty_iff_eq_empty] at has
    subst s
    exact .of_forall fun u=>.of_forall fun c=>by
      intro f K N per cf fk ck live heat optical req age panel z held uk M
      letI:IsProbabilityMeasure (scene (A) N per K):=OPE.Therm.probability R.makes.wilson live
      have blank:M=(fun _=>1):=by funext U;simp [M,field]
      rw [blank,actualTransport_const (C) R.makes live (1:ℂ) uk 1]
      simp only [integral_const,probReal_univ,one_smul,sub_self,norm_zero]
      exact one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans ((A).levels.fits.delayed f).le) _)

theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(simple:G.Simple)
    (purchase:RG05Preconstruction.ReadoutPurchase R.b)(storage:RG05Readout.Many.Storage (C) R.doors)
    (cater:Cater (C) R.doors)(tabs:Stock.Tabs (A).levels)(d:Fin n→ℕ)
    (j q aperture pow:ℕ)(B:ℝ)(non:0≤B)(ceiling:∀i,((A).levels.budget i).supportExponent=100):
    ∀ᶠ u:ℕ in atTop,∀ᶠ c:ℕ in atTop,∀s:Finset (Fin n),Fee R u c q aperture pow B d s:=by
  filter_upwards [eventually_all.2 (fun s=>mask R book simple purchase storage cater tabs d s j q aperture pow B non ceiling)]
    with u active
  exact eventually_all.2 active

end YM.Integration.WilsonOriginalPublicTrialPhaseUncutField
end
