import YM.Integration.NativePreselectedPostnumericPeriodRun
import YM.Integration.WilsonWindowSelectionClock

/-! Original Wilson campaign selection with the marked-window invoice.
Physical choices follow YM.Integration.NativePreselectedPostnumericPeriodRun; see the source map. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.RG05Preconstruction
open YM.Integration.WilsonLimitConstruction
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Campaign
set_option quotPrecheck false
open Boutique
open Daisy.Charity.RG12
universe v


/-- The same original Run, now retaining the native profile order bounds. -/
theorem selectRunAtPhysicalMenu (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ Ξ : Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL : EventuallyPaid Ξ)
    (hfinish : ∀ a, Ξ a → YM.Integration.NativeFVAPlateau.Funded a → Λ a)
    (Demand : Sheet G → Precision.MapPrices → Type v) (hDemand : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R:Run G)(T:Campaign R), prediction R.kit ∧ R.family.path.levels.clock.kernel.penalty=b ∧
      PostnumericPreselection Demand extra numeric postnumeric R ∧
      (∀ j, j ≤ (R.metals.p.profile j).order ∧
        j ≤ (R.metals.p.profile j).power) ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      YM.Integration.CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧ ReadoutPurchase R.b ∧
      ∃ Θ v, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v := by
  let Q (i:ℕ):= i+2
  obtain ⟨s,T0,chosen,n,M,P,A,X,Y,K,c,hPrediction,hFloor,hExtra,hSheet,hKernel,hNumeric,hPost,hStage,hOrders,H,hAmp,hWild,hB,hF,hP,hX,hT,hY,hK,hQ,hHalo,hΛ,hTreasury,hPeriod,hA,
    ξ,v,t,a,D,Φ,θ1,hCustody,hν,hφ,hv,hψ,UΩ,hP',hZ⟩ := allFactorAtPhysicalMenu (Ω:=Ω) (ℋ:=ℋ) h hb Δ Q (fun i j hij=>Nat.add_le_add_right hij _) (fun _=>Nat.le_add_left ..) Λ Ξ hL hfinish Demand hDemand extra numeric postnumeric (@prediction) paid
  obtain ⟨R,T,hPredictionR,hMetals,hR,hG,hN,hW,hU,hK',hA',hAddr,hlim,hS,Θ,hcR,hΘ⟩ :=
    engageWithCustodyFactor (Ω:=Ω) (ℋ:=ℋ) h Δ (q:=Q) (tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id) hA hQ hK hY hX Φ H hAmp hWild θ1 UΩ hCustody hν hφ hP' hv hψ hZ (@prediction) hPrediction
  rw [← hW] at hB hF hHalo hT hΛ hTreasury hPeriod hP hNumeric hPost hStage
  have hSelected : PostnumericPreselection Demand extra numeric postnumeric R := by
    refine ⟨s, T0, chosen, n, hFloor, hExtra, ?_, ?_, hNumeric, hPost, hStage⟩
    · rw [hMetals]
      exact hSheet
    · rw [hMetals]
      exact hKernel
  have hRunOrders : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power := by
    rw [hMetals]
    exact hOrders
  have hPeriodR : YM.Integration.CommonPeriodPurchase.Funded
      R.metals.K R.metals.O R.family.path.levels := by
    rw [hMetals]
    exact hPeriod
  exact ⟨R, T, hPredictionR, hB, hSelected, hRunOrders, hΛ, hTreasury, hPeriodR, hN,
    { localBudget := hK'.original
      attentive := hA'
      logCopy := hlim
      locrian := hR
      wild := hG
      silk := hS
      poly := hU
      fixed := hAddr
      tic := hT
      halo := hHalo
      paced := hF
      stoves := hP
      hasSky := ⟨UΩ, Θ, hΘ⟩ }, hK'.news, hK'.readout, ⟨Θ, UΩ, hcR, hΘ⟩⟩


end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
end

