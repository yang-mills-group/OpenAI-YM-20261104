import YM.Integration.WilsonLongContactUnaryBallot
import YM.Integration.ManuscriptQLocalMarkedRoster

/-! The genuine singleton in each marked finite ticket, with its complete former source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactPriorBallot
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators

open RG.Shoot Marker Overlay RG3.Held RG3.Forms RG3.Script.Picnic Push.AbsoluteSums LocalComparison
open Progress.DirectedRecipe MergeProof MergeProof.Menu ManuscriptQLocalMarkedRoster
open ManuscriptQLocalMarkedLeaves ManuscriptQLocalMarkedOffers
open Merge Merge.Palette PhysicalNext.Repeat.WilsonLongContactUnaryAverage RGLocalTaylor
variable {G : Gauge} {c f L : Side} {S : StepData c f} {Y : Rep G f} {T₀ : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ α : ℝ} {o : Target.Order G W}
    {X V : Type} [DecidableEq V] {Γ : Census V} {seats : V → Site f}
    {T : Taste X seats Y Γ} {w : V → ℝ} {κ a b : ℝ} (B : FullBudget Y.p T w κ a b)
    (H : Cash W x μ L Q o α T₀ (QLocalInheritedRegularSlots.carrier Y))
    (base y : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ))

theorem original (i : ↥E) (part : Bool) (χ : Chi) (U : Config G c) :
    let idx : (Occurrence E (live (T:=T) K))×Bool := (.inl i,part)
    let M:=fun j=>((ManuscriptQLocalMarkedRoster.promised B base y E K).terms j).M
    ∃ k:ℕ,(M idx).turn=.logKey k ∧ (M idx).crest=(T.menu.branch i) ∧
      authorized H (solitary S (M idx)) ∧ Mayer.Start (solitary S (M idx)) ∧
      Palette.act M H χ U (solitary S (M idx)) (Tickets.mono (Palette.sign M S) idx)=
        masked (Pressure.temp x) (Brim.plate H k).support
          (fun Z=>branch (T:=T₀) (Q:=Q) (x:=x) (o:=o) (W:=W) (M idx) χ Z) U := by
  classical
  let idx : (Occurrence E (live (T:=T) K))×Bool := (.inl i,part)
  let M:=fun j=>((ManuscriptQLocalMarkedRoster.promised B base y E K).terms j).M
  have placed:=((ManuscriptQLocalMarkedRoster.promised B base y E K).place (.inl i) part).1
  change (M idx).turn=(ordinary B base y i.val).turn at placed
  obtain ⟨k,hk⟩ : ∃ k:ℕ,(ordinary B base y i.val).turn=.logKey k := ⟨_,rfl⟩
  have key: (M idx).turn=.logKey k := placed.trans hk
  have plot : (M idx).crest=T.menu.branch i := by
    change (M idx).turn.support _=_
    rw [placed,ordinary_support]
  have start:=WilsonLongContactUnaryBallot.admitted H M idx k key
  have allowed:=start.2.1
  have initial:=start.2.2
  rw [start.1] at allowed initial
  exact ⟨k,key,plot,allowed,initial,WilsonLongContactUnaryBallot.full H M idx k key χ U⟩

end YM.Integration.WilsonLongContactPriorBallot
