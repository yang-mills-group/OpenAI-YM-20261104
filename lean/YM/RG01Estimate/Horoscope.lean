import YM.RG01Estimate.Songster
import YM.RG01Estimate.ScopeWork
/-! # Replenish with E-star present. Requires preserved int projection on the tube.
 Does not need basis comparison between different Ledgers. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Board
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {c f:Side}{N m n i j r:ℕ} (Hm:m < N) (V : f.val=c.val*(U.B.a.S.block m).val) (F:Forest (Pane.panel U m V).ratio)
local notation "Γ" => U.B.a
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "A₀" => U.B.a.clock.adm (m+1)
local notation "x" => U.B.a.clock.hatBeta m
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => U.B.a.budget m
local notation "B'" => U.B.a.budget (m+1)
local notation "P₀" => Mural.sheet X.p D (U.B.a.clock.adm (m+1))
local notation "R₀" => R.target J I
local notation "W" => R.shape
local notation "𝕊" => Pane.panel U m V
local notation "Φ" => (Pane.orchestra U N V)
local notation "χ" => Chi.canonical
local notation "Z'" => R.expense J I
local notation "γ" => U.B.kin.alpha N m
local notation "σ" => X.p.profile (U.B.a.clock.J m)

variable (Y : RG.Rep G f)
lemma authorizes (he:100*(1+radiusB (U.B.a.clock.hatBeta m)) ≤ c.val) (ht:Y.beta∈ Shoot.band U.B.a (m+1))
    (hp:Y.path=(Φ).up) (hg:Y.clip=(Φ).high) (h: Y.p=B') (hζ: Y.activities.Valid Y.p (U.B.a.clock.allowance (m+1)) (U.B.a.clock.forcedAllowance (m+1))) (hm:m<N):
   ∃ (V : Boulevard.Chartlet R.shape U N m V Y), Cash.Renewed (Z').degrees (Z').earn (Z').one (Z').two V:= by
    have hs:= Pane.accepts U N V hm he
    apply ((R.shape.consumes J I (PriceCompiler.step_paid U.B.a m)).2.2.2 x ((R.pledging.conducts.income.grow.1 _).trans (U.B.valid.pays m))).2 _ _ _ Φ hs|>.2 (ovation U N V hm R.pledging.conducts.full) Y
    have hy := ingots U N V hm he ht; obtain ⟨hr,hK,hY,hX,hQ,hF,hB⟩:=hy
    have hv : betaF G x (𝕊).patch.L=U.B.a.clock.hatBeta (m+1):= (Application.clock_next U.B.a m 0).symm
    refine ⟨hr,⟨hp,hg,h ▸ hK.temp⟩,⟨by rw [hp,hg]; exact hY.paths,?_⟩, h ▸ hX,hQ,h ▸ hF,hB⟩
    unfold incomingE incomingK Delay.fineMonitor; rw [hv]; exact hζ

variable {Y}
section pruner
variable (H : Chartlet R.shape U N m V Y) (h : SeekR R.shape U N m V H) (S : Match.Alliance H H 1 0)
    (hS : S.units=Equiv.refl _) (hΦ : Routed.Allowed R) (hn : 2 ≤ r) (hk : r ≤ U.B.a.clock.J (m+1))
    {ε θ τ t' u' : ℝ} {E:Set ℕ} (hΙ: preExponent (U.B.a.budget m) ≤ θ) (hτ : Inherit.Debits Y E (Fate.debt r G (D.L (U.B.a.clock.J (m+1))) (U.B.a.clock.hatBeta m))) (he': Single.Pays H (U.B.a.budget m) E Chi.canonical θ ε) -- aux τ can be selected tail nonzero
local notation "P" => (Beam.marquee H B)
include Hm R h
-- ANY surrendered
lemma direct (V':Config G c) : earlyValue P (U.B.kin.path N m) (U.B.a.params m).clip B (Song.plusone H S χ γ) Y.beta (Song.weighty H χ F) γ V' = (Pane.panel U m V).push Y.beta Y.eval V' :=
    Eq.trans (Beam.travels H (B) _ _ _ _ V') ((lays R.shape U V S R.inn.chip Hm R.pledging.jewels R.pledging.conducts.full (R.pledging.agenda _ _ (step_paid (Γ) m)|>.1) (CensusStep.decent R Hm) h F).2 V').symm

lemma all_pay : Collection.Local (P) B (Song.plusone H S χ γ)
      (turnFee B*(betaF G x L ^ (Z').wanting + betaF G x L ^ (-(7/16):ℝ))) (CensusStep.hardCost R m):= by
   let hi : StepStages J I := step_paid U.B.a m
   have hp := U.B.valid.pays m; have hu:= Pane.ovation U N V Hm R.pledging.conducts.full
   obtain ⟨y,d,v,t,a,b,r,B₀,q,i,n,N',hC,hY⟩:= (R.pledging.jewels J x hp I hi).2 _ _ _ Φ H.laws.data.funds hu Y H
   obtain ⟨N',hk⟩:= N'
   have hR: U.B.a.params m=σ := params_eq U.B.valid m
   have hθ : preExponent B ≤ (Z').earn := by unfold preExponent; rw [show (B).supportExponent=(σ).supportExponent from congr_arg RG.Stage.supportExponent hR]; exact R.pledging.agenda _ _ hi|>.1
   have hQ:(B).order=(σ).order:=congr_arg RG.Stage.order hR
   have hB:(B).power=(σ).power:=congr_arg RG.Stage.power hR
   have hD:= Boulevard.suns R.shape U R.inn.chip Hm V H; have he: (Φ).down.Bounds (Φ).low (U.B.a.params m).width (U.B.a.params m).paths (U.B.a.clock.loopCap m):= U.B.support.cap _ _ Hm.le
   have hf:= (U.B.a.params m).width_pos
   have hv:=VacuumListing.full H (B) Chi.canonical S N' rfl hQ.le hB.le rfl hθ h hC γ he (CensusStep.decent R Hm) (hD.1.trans (show _/4≤(U.B.a.params m).width/2 by linarith))
   exact VacuumListing.relax B hv (mul_le_mul_of_nonneg_left (add_le_add hY hD.2.1) (turnFee_pos _).le) (le_refl _)

include hΦ hS hn hk hΙ he' hτ
lemma fulfilled : Collection.Local (P) B (Pruned.high H χ S E r γ) (turnFee B*ε+Routed.spill (A:=U) m r) (CensusStep.hardCost R m) := by
   have hi : StepStages J I:= step_paid (Γ) m; have hR : U.B.a.params m=σ:= params_eq U.B.valid _
   have hz:= hΦ J x (U.B.valid.pays m) I hi (first_le U.B.valid m) r hn hk
   obtain ⟨hV,hB,hD,hΨ,hK⟩:= hz
   have hg: preExponent B ≤ (Z').earn:= by
      unfold preExponent; rw [show (B).supportExponent=(σ).supportExponent from congr_arg RG.Stage.supportExponent hR]; exact R.pledging.agenda _ _ hi|>.1
   have hp := H.laws.intake
   have hx : |Y.beta|≤ 2*betaF G x L:= by rw [abs_of_nonneg hp.positive.le, ← H.laws.data.funds.length_eq]; exact H.laws.intake.window.2
   have hC : (Φ).down.Bounds (Φ).low (U.B.a.params m).width (U.B.a.params m).paths (U.B.a.clock.loopCap m):= U.B.support.cap _ _ Hm.le
   have hf:(B).threshold ≤ 2*Pressure.fiery G x L:= H.laws.data.funds.length_eq ▸ H.laws.data.room.temperatures
   have hQ:(B).order=(σ).order:= congr_arg RG.Stage.order hR
   have he:(B).power=(σ).power:= congr_arg RG.Stage.power hR
   obtain ⟨hO,hx'⟩:=hD B hf he hQ (congr_arg RG.Stage.supportExponent hR) rfl Y.beta γ (U.B.a.clock.loopCap m) hx (Boulevard.coupling U _ _ Hm) (coverBill U.B.a m|>.1) ((coverBill _ _|>.2).trans (brace _ hK))
   -- keep Path oriented
   have hσ : preExponent B /(B).B ≤ (U.B.a.params m).width/4:= hR ▸ hx'
   have hΩ : Real.exp (-((U.B.a.params m).width/4)*(B).B)*Song.octaveNeed G B (U.B.a.params m).clip (U.B.a.params m).width (U.B.a.params m).paths (U.B.a.clock.loopCap m) Y.beta γ ≤ Fate.target r G L x:= by rw [hR]; exact hO
   have hp:= (Pruned.account H B χ S E r γ rfl rfl hS hV (Pane.ovation U N V Hm R.pledging.conducts.full) hQ.le he.le h hC (CensusStep.decent R Hm) hσ hg hΩ hΙ hτ he').1
   refine VacuumListing.relax B hp ?_ (le_refl _)
   rw [Routed.spill,PriceCompiler.beta_eq U.B.valid m]; let A:= Fate.target r G L x; have hh:turnFee B= Height.away (σ):= by unfold turnFee Height.away; rw [hQ,he]
   have ht := hΨ.1
   rw [hh]
   calc _ = Height.away (σ)*ε + Height.away (σ)*(A+A+A):= by unfold A; ring
        _ ≤ _ := add_le_add le_rfl ht

omit Hm hΦ hS hn hk hΙ he' hτ
lemma intact : ∃ k':ℕ→ℝ,(∀ i,0 ≤ k' i∧∀ V,‖(Pruned.high H χ S E r γ).hardRead i V‖ ≤ k' i) ∧
     Ac.Hit (fun i=> ((Beam.marquee H B).hard i).support) (B).B k' ((B).supportExponent+1+1) (CensusStep.hardCost R m) := by
   have hR : U.B.a.params m=σ:= params_eq U.B.valid _
   have hi : StepStages J I:= step_paid (Γ) m
   have hθ: (B).supportExponent+1+1 ≤ (Z').earn := by
      rw [show (B).supportExponent=(σ).supportExponent from congr_arg RG.Stage.supportExponent hR]; linarith only [(R.pledging.agenda _ _ hi|>.1)]
   exact Refrain.chargesOut (Marlin.raiser B) H S χ h rfl hθ
end pruner
end YM.RG01Estimate.Board
