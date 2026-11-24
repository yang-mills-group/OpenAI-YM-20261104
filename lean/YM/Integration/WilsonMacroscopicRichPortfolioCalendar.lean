import YM.Integration.WilsonMacroscopicRichPortfolioCapture

/-! All signed physical leaves pay for one true source and one terminal counterterm at every lower date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichPortfolioCalendar
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) {b N per:ℕ}
set_option quotPrecheck false
local notation "C" => R.family
local notation "A" => (C).path
local notation "Y" => (C).path.rep N per
local notation "S" => (A).levels.clock.op b per
local notation "bill" => bling (A).levels b

open RG16.Literal
open Trace.Physical.GermGraph Extra.Histories.Relay

open WilsonLimitConstruction PhysicalNext
universe u

theorem original (simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T){δ:ℝ}
    (fund:FundedOriginalProperties.{u} simple δ W) (h m:ℕ) (start:(C).ref h ≤ m) (mb:m ≤ b)
    (top:b<N) (eligible:h+3 ≤ (A).levels.clock.J b) (η:ℝ) (ηpos:0<η)
    {I:Type} [Fintype I](o:I → Site ((C).side (b+1) per)) (home:∀i,(S).ratio.parent (o i)=0)
    (X:I → Three G ((C).side (b+1) per)) (valid:∀i,Useful (Y (b+1)) (X i))
    (v:I → ℝ) (raw:∀i,MergeProof.Float.Blade (Y (b+1)) (o i) (X i).2.1
      (profile (Y (b+1)).activities (X i).2.2) 0 (v i)) (pos:∀i,0 ≤ v i)
    (f:I → Cut C N per)(cont:∀i,Continuous (f i))(actual:∀i,(X i).1=credit C N per 0 (f i) (b+1) top)
    (weights:I → ℂ):
    let Φ:=∑i,weights i • f i
    let fee:=(C).S.a (b+1)^h*bill*∑i,‖weights i‖*v i
    let E:=WilsonMacroscopicRichCaptureFilingBudget.capital C b fee η
    (∃ K:Coefficient ((C).labels.level h) ((C).side b per),K.Format 0 (C).params (Y b) ∧
      K.remBound 0 (Y b) (kappa A b) fee ∧ ((C).labels.level h).coeffSize K.x ≤ fee ∧
      credit C N per h Φ b top.le=K.density 0 ((C).localSection h) (Y b)) ∧
    ∃ z:(C).label h, Next.UVStress.quota C h b N per z ≤ 2*E ∧
      ∀(j:ℕ),m ≤ j → ∀(jb:j ≤ b)(door:Opened C h j per),
        Booked C N per h Φ j (jb.trans top.le) ∧
        mCost C h N per j (topReport C N per h R.makes j door (jb.trans top.le) Φ-
          ((C).factory h N per).terminal.symm z) ≤ E/gainChart A b j:=by
  classical
  intro Φ fee E
  have tiers:=(WilsonCloseCaptureFinances.original R simple W fund).2
  have member(i:I):= (WilsonMacroscopicRichGradedCapture.original R h tiers top eligible (home i)
    (X i) (valid i) (raw i) (pos i) (f i) (cont i) (actual i)).1
  choose Q rows using member
  have joined:=WilsonMacroscopicRichPortfolioCapture.merged R.family N per h b R.makes (start.trans mb)
    top.le weights f cont _ Q rows
  have cash:(∑i,‖weights i‖*((C).S.a (b+1)^h*(bill*v i)))=fee:=by
    dsimp only [fee];rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _=>by ring
  rw [cash] at joined
  obtain ⟨K,fmt,rem,size,source⟩:=joined
  have upper:Continuous Φ:=by
    have form:Φ=fun U=>∑i,weights i*f i U:=by
      funext U
      dsimp only [Φ]
      rw [Finset.sum_apply]
      rfl
    rw [form]
    exact continuous_finsetSum _ fun i _=>continuous_const.mul (cont i)
  exact ⟨⟨K,fmt,rem,size,source⟩,
    WilsonMacroscopicRichEnrolledFiling.original R.family N b m per h R.makes
      (R.again simple).1.scrim Φ upper K fee η ηpos start mb top.le fmt rem size source⟩

end YM.Integration.WilsonMacroscopicRichPortfolioCalendar
