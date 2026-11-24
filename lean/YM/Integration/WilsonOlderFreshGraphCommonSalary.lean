import YM.Integration.WilsonOlderFreshGraphAllStages

/-! Every independently normalized input, at every finite order and loan,
is offered at a subpower amplitude cost on a single original selected
physical school before the cutoff, period, test film or insertion site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCommonSalary
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical

open WilsonOlderFreshGraphAllStages WilsonOlderFreshGraphSubmit
open WilsonOlderFreshGraphCompiler
variable {G:Gauge} (R:Run G)(L:Primer.Families R.family)(a:hue G)(simple:G.Simple)

def Offered (S:Query)(dmax i:ℕ)(depth:S.letter.toll<dmax)
    (w:Letter (R.family.labels.level S.letter.toll))(σ δ:ℝ):Prop:=
  ∀p:Ballot i dmax,∃ T:WilsonOlderFreshGraphSlate.Copy G S.letter.toll S.order σ,
    (∑j,T.fare j) ≤ (R.alloy.B.a.clock.hatBeta i)^δ*(1+‖Annex.compress dmax p.2‖) ∧
    WilsonOlderFreshGraphDatedSalary.Published R L a depth i w p T

theorem original {φ U:ℕ→ℕ} (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (WilsonOlderFreshGraphAllStages.menu G)
        simple (WilsonOlderFreshGraphMatrixPrice.jointLaw law)) (@WilsonWindowFormalPurchase.Canonical G U) R.kit):
    let M:=WilsonOlderFreshGraphAllStages.menu G
    let H:=roots M simple R.metals.p R.metals.K
    (∃ books,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) books) ∧
    ∀(S:Query)(D:ℕ)(depth:S.letter.toll<D)(_:Loc G 1)(w:Letter (R.family.labels.level S.letter.toll))
      (δ:ℝ),0<δ→∀ᶠ i:ℕ in atTop,∀k:ℕ,k ≤ R.alloy.B.a.clock.J i→1 ≤ Burn.horizon k→
        Offered R L a S D i depth w (Agenda.seed H φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) δ:=by
  intro M H
  obtain ⟨school,rootsPay⟩:=WilsonOlderFreshGraphAllStages.original simple R law purchase
  refine ⟨school,?_⟩
  intro S D depth o w δ positive
  let d:=S.letter.toll
  let Q:=S.order
  obtain ⟨B,v,b0,submission⟩:=WilsonOlderFreshGraphSubmit.original R L a depth simple purchase.2 o w Q
  have active:Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  filter_upwards [submission,WilsonOlderFreshGraphPublication.original R L a depth simple purchase.2 o w,
    eventually_ge_atTop 1,active.eventually_ge_atTop S.name,WilsonOlderFreshGraphSubpower.on_run R simple B v b0 positive]
    with i incoming net late live budget
  obtain ⟨b,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
  intro k fit hk p
  let σ:=Agenda.seed H φ (Burn.horizon k) (R.alloy.B.a.clock.J (b+1))
  let βhat:=R.alloy.B.a.clock.hatBeta (b+1)
  let x:=R.alloy.B.a.clock.J (b+1)
  let K:=R.metals.p.kernel
  let a₀:=WilsonOlderFreshGraphPainter.width G K d Q x
  have radius:WilsonOlderFreshGraphRoster.narrow R d Q (b+1)=a₀:=by
    unfold a₀ K x WilsonOlderFreshGraphRoster.narrow WilsonOlderFreshGraphPainter.width
    have idK:R.family.path.levels.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
    rw [idK];rfl
  rw [radius] at incoming
  obtain ⟨t,exactBank,wage⟩:=incoming p
  let J:=WilsonOlderFreshGraphMatrixPrice.printer G S.letters d Q rfl K x
  obtain ⟨reach,cap⟩:=rootsPay S b k fit hk live
  let T:=WilsonOlderFreshGraphDatedSalary.reprint J t S.letter.higher σ reach
  refine ⟨T,?_,?_⟩
  · have hJ:1+J.cap ≤ Real.sqrt (Real.log βhat):=Real.le_sqrt_of_sq_le cap
    have keep:=J.uniform t
    rw [wage] at keep
    have day:0 ≤ 1+roof (d:=d) (Q:=Q) B v βhat*‖Annex.compress D p.2‖:= by
      change 0 ≤ 1+roof B v (R.family.path.levels.clock.hatBeta (b+1))*‖Annex.compress D p.2‖
      rw [←wage];linarith [t.wage0]
    have spend:=keep.trans (mul_le_mul_of_nonneg_right (by linarith:J.cap ≤ Real.sqrt (Real.log βhat)) day)
    exact spend.trans (budget _ (norm_nonneg _))
  · intro j n A s
    have named:=net p.1.1 p.1.2 p.2 j.val n A s
    have read:=J.reading j.val (Nat.le_of_lt_succ j.isLt) t n A s
    rw [exactBank] at read
    exact named.symm.trans (read.trans (Fin.sum_univ_eq_sum_range (fun l:ℕ=>
      ((J.emit l t).folded l j.val).table n (mingle A s)) (Q+1)).symm)
end YM.Integration.WilsonOlderFreshGraphCommonSalary
end
