import YM.Integration.WilsonSeparatedOriginalSlabFieldPanel
import YM.Integration.WilsonMacroscopicRichPortfolioCalendar

/-! One original label on every earlier open filing chart for the signed, jointly tested physical cutoff field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFiledFilm
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open RG16.Literal Trace.Physical.GermGraph Extra.Histories.Relay WilsonLimitConstruction PhysicalNext
open WilsonSeparatedOriginalSlabFieldPanel WilsonReportHarvestSlabLabels
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G:Gauge}(R:Run G){b N per:ℕ}
set_option quotPrecheck false
local notation "C"=>R.family
local notation "A"=>(C).path
local notation "Y"=>(C).path.rep N per

/-- The quota is attached to a single actual original terminal label before the choice of the earlier filing date. -/
def Filing (f:Cut C N per)(u₀ h:ℕ)(top:b<N)(η bound:ℝ):Prop:=∃fee:ℝ,fee≤bound ∧
  (∃K:Coefficient ((C).labels.level h) ((C).side b per),K.Format 0 (C).params (Y b) ∧
    K.remBound 0 (Y b) (kappa A b) fee ∧ ((C).labels.level h).coeffSize K.x≤fee ∧
    credit C N per h f b top.le=K.density 0 ((C).localSection h) (Y b)) ∧
  ∃z:(C).label h,let E:=WilsonMacroscopicRichCaptureFilingBudget.capital C b fee η
    Next.UVStress.quota C h b N per z≤2*E ∧ ∀j,u₀≤j → ∀(jb:j≤b)(door:Opened C h j per),
      Booked C N per h f j (jb.trans top.le) ∧ mCost C h N per j (topReport C N per h R.makes j door
        (jb.trans top.le) f-((C).factory h N per).terminal.symm z)≤E/gainChart A b j

theorem original (simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T){δ:ℝ}
    (fund:FundedOriginalProperties.{u} simple δ W)(h u₀:ℕ)(start:(C).ref h≤u₀)(ub:u₀≤b)
    (top:b<N)(eligible:h+3≤(A).levels.clock.J b)(η:ℝ)(ep:0<η)(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette C (s i))
    {f:Cut C N per}{rent unit:ℝ}(up:0≤unit)(P:Panel R s v top unit f rent):
    Filing R f u₀ h top η (abs ((C).S.a (b+1)^h*bling (A).levels b)*rent*unit):=by
  letI:=P.finite
  let F:=fun i:P.I=>word R (N:=N) s v (P.site i) (P.test i) entire
  choose X clean actual raw using (fun i:P.I=>P.filed i entire)
  let ratio:=((A).levels.clock.op b per).ratio
  have origin:ratio.parent 0=0:=(show ratio.embed 0=0 from ratio.root.map_zero) ▸ ratio.embed_parent 0
  have paid:=WilsonMacroscopicRichPortfolioCalendar.original R simple W fund h u₀ start ub top eligible η ep
    (fun _:P.I=>0) (fun _=>origin) X clean (fun _=>unit) raw (fun _=>up) F
    (fun i=>continuous_word R s v (P.site i) (P.test i) entire) actual P.weights
  let q:=(C).S.a (b+1)^h*bling (A).levels b
  change Filing R f u₀ h top η (abs q*rent*unit)
  rw [P.exact]
  refine ⟨q*∑i,‖P.weights i‖*unit,?_,paid⟩
  rw [←Finset.sum_mul,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) P.bound (Finset.sum_nonneg fun _ _=>norm_nonneg _) (abs_nonneg _)) up

end YM.Integration.WilsonSeparatedOriginalSlabFiledFilm
