import YM.Integration.WilsonIndependentRestoredMatrixCampaign
import YM.Integration.WilsonPhysicalPositionWeakRoofGrant

/-! The actual surveyed matrix seller and both original weak purchases on a single Wilson sheet. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.WilsonLimitConstruction
open YM.Integration.RG05Preconstruction
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open YM.MergeProof.East
-- Another grantor for buying universal weak supplies. Can still extend before-L clocks, after-L Delays, extra Paid W and layouts. retains
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
open Next.Rank Next.Rank.East
include hp hQ hQ' hG
theorem ReporterRoofs.matrix (ν:Side→ℕ→ℕ→ℝ) (hν:∀L j d,0<ν L j d) (Ω : RemainderComparison.Chron.Contemple G) {ξq ωt ωv:ℝ} (θ1:Luna.Tableau ξq 300) (hu:Jams.sphere ξq ωv ωt) (hQ2:∀ i,2≤ Q i)(he:∀ i,100 ≤ v.supportExp i) (Δ:Daisy.Charity.RG12.Decal G)
    {budget : ℕ → ℝ} {claim : FundedCompanySelection.Prediction G}
    (seller : YM.Integration.WilsonMatrixTicketLengthsLender.Auction G K v budget (@claim))
    (chop : Chop seller.sheet budget mile)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) : let s := seller.sheet; let T := seller.price; let Y := budget; let K' := seller.worth; ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.bountyV s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), seller.allowed k P → ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),((claim X ∧ prediction X) ∧ AcrossPanels X ∧ ReporterRoofs.Roofed X) ∧ (X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J' ∧ Jams.Degree X.shape X.scout V' ∧ Jams.Savvy X.scout X.target V' ξq ωv ωv ωt ∧ Roof.Roofing X ωt ωt ∧ Planned.Port.AtTop B.kin ∧ Stationary.Artes.Cadre F B.kin ∧ Next.Free.Amplify B.M ∧ Jams.PaysW X.shape ωv V' ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) V' ∧ (∀ i:ℕ,100 ≤ (B.a.budget i).supportExponent) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ (∃ U₁, FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 U₁ P.L ∧ Mallow.Canyon ξq X.shape Y θ1 U₁ V') ∧ Jams.Wild X.shape V' ∧ Mallow.AccordV X.shape Q V')∧∃ (b:Bandage X Y K'), RestoredBooking ν b ∧ YM.Integration.RG05Preconstruction.Extras Ω Δ b ∧ Unlatched b Q (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, CompleteWeak Z f ∧ Trace.Over.Gallery Z f) := by
  intro s T Y K'
  have hv:=seller.stage
  obtain ⟨τ,hτ,core⟩:=restoredMatrixPanelCampaign (ν:=ν) (hν:=hν) (Ω:=Ω) hG hp Q hQ hQ' θ1 hu hQ2 he Δ seller chop (@prediction) paid
  have cofinal:Tendsto (fun i=>(s.profile i).order) atTop atTop:=
    tendsto_atTop_mono (f:=id) (g:=_) (fun i=>by
      rw [hv.jets]
      exact (le_max_right ..).trans (hp.k i)) tendsto_id
  obtain ⟨m,charge⟩:=WilsonPhysicalPositionWeakRoofSchedule.original s (ThroughLaunch.raging s T) cofinal
  obtain ⟨O⟩:=Next.Rank.exists_budget G
  let z (d:ℕ):=∑ i∈Finset.range (d+1),generator G i
  have income (i d:ℕ) (hi:i≤d):generator G i≤z d:=
    Finset.single_le_sum (fun i _=>by unfold generator;positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have z0 (d:ℕ):0≤z d:=Finset.sum_nonneg (fun i _=>by unfold generator;positivity)
  refine ⟨τ⊔m,hτ.trans le_sup_left,fun k hk=>?_⟩
  obtain ⟨old,requested⟩:=sup_le_iff.mp hk
  obtain ⟨existsRolls,rolls⟩:=core k old
  intro M
  have menu:WilsonPhysicalPositionWeakRoofSchedule.Asked M.p M.K m:=by
    obtain ⟨a,grow,large,checks,P,F,ask,arc⟩:=charge.menu
    refine ⟨a,grow,large,checks,P,F,⟨ask.later,?_,ask.pin⟩,arc⟩
    intro i j hij x
    obtain ⟨order,paid⟩:=ask.costs i j hij x
    refine ⟨order,fun d hd L hL=>?_⟩
    have p:=paid d hd L hL
    exact ⟨p.reg,p.coast,p.commission,p.merit⟩
  refine ⟨existsRolls,fun P allowed=>?_⟩
  obtain ⟨U,issued⟩ := rolls P allowed
  refine ⟨U,fun w hw Q₀ e=>?_⟩
  obtain ⟨F,g⟩:=issued w hw Q₀ e
  refine ⟨F,fun u0 positive=>?_⟩
  obtain ⟨θ,θpaid,hB⟩:=g u0 positive
  refine ⟨θ,θpaid,fun Ht J T0=>?_⟩
  obtain ⟨V,hV,room⟩:=hB Ht J T0
  refine ⟨V,hV,fun V' advance D W=>?_⟩
  obtain ⟨Z,hZ,paidZ⟩:=room V' advance D W
  obtain ⟨a,grow,large,W0,hl,hr,hw,bank⟩:=WilsonPhysicalPositionWeakRoofSchedule.paid M.K m menu O
    (Next.Foundations.chart G) (Next.Foundations.chart_ok G)
    (fun i=>(requested i).trans (P.large i).need) hG z z0 Z
  refine ⟨W0,⟨hZ.1.trans hr,hZ.2.1.trans hl,hZ.2.2.trans hw⟩,fun W ha hb hc A active div=>?_⟩
  obtain ⟨T',B,hF,X,old,hR,b,restored,hExt,hAll⟩:=paidZ W (hr.trans ha) (hw.trans hb) (hl.trans hc) A active div
  refine ⟨T',B,hF,X,⟨old.1,old.2,?_⟩,hR,b,restored,hExt,hAll⟩
  refine ⟨O,z,a,income,grow,large,fun C same binding prices makes parade d=>?_⟩
  apply bank C ?_ binding prices makes parade d
  rw [same]
  exact retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid


end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint

