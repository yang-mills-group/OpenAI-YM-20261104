import YM.Integration.WilsonOlderFreshGraphMatrixPrice

/-! The original cap passed to the native physical voter is at most
sqrt(log hatBeta) times the actual normalized film and polynomial age bill.
The same publication hears every position and arbitrary finite torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphDatedSalary
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
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

open WilsonOlderFreshGraphAward
include simple



open WilsonOlderFreshGraphCompiler WilsonOlderFreshGraphSubmit WilsonOlderFreshGraphSlate
open AllOrder.Ink.Money
omit simple in
def reprint {q h:ℕ} {G:Gauge} {a:ℝ} {I:Unit→Loan}
    (F:WilsonOlderFreshGraphCompiler.Press G I h q a) (T:Submission G h q a)
    (d0:0<h) (σ:ℝ) (attain:2*σ ≤ strip I q a): WilsonOlderFreshGraphSlate.Copy G h q σ where
  roll:=fun j=>F.emit j.val T
  fare:=fun j=>F.rental j T
  positive:=d0
  legal:=fun j=>(F.priced j T).2
  paid:=fun j=> by
    have h:=(F.priced j T).1
    refine ⟨h.pinned,Push.Local.sumBudget_mono h.price (fun u=>Lantern.fee_nn ..) (fun u=>?_) le_rfl⟩
    unfold Roll.price Lantern.money
    have ht:=Texture.mag_nonneg ((F.emit j.val T).leg u).atom
    gcongr

def Published (i:ℕ) (w:Letter (R.family.labels.level d)) (p:Ballot i D) {Q:ℕ} {σ:ℝ}
    (T:WilsonOlderFreshGraphSlate.Copy G d Q σ):Prop:=
    ∀j:Fin (Q+1),∀(n:Side)(A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
            probe R L a depth i w p n s j.val A =
              ∑l:Fin (Q+1),((T.roll l).folded l.val j.val).table n (mingle A s)

theorem original {φ U:ℕ→ℕ} (I:Unit→Loan)(Q:ℕ)(level:(I ()).toll=d) (d0:0<d)
    (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ
      (WilsonOlderFreshGraphMatrixPrice.menu G I d Q level) simple (WilsonOlderFreshGraphMatrixPrice.jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (o:Loc G 1)(w:Letter (R.family.labels.level d)):
    let M:=WilsonOlderFreshGraphMatrixPrice.menu G I d Q level
    let H:=roots M simple R.metals.p R.metals.K
    (∃ books,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) books) ∧
    ∃(B:Fin (d+Q+1)→ℝ)(v:Fin (d+Q+1)→ℕ), (∀r,0≤B r) ∧
      ∀ᶠ i:ℕ in atTop,∀(k:ℕ),k ≤ R.alloy.B.a.clock.J i→1 ≤ Burn.horizon k→
        let σ:=Agenda.seed H φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
        let βhat:=R.alloy.B.a.clock.hatBeta i
        ∀p:Ballot i D,∃ T:WilsonOlderFreshGraphSlate.Copy G d Q σ,
          (∑j,T.fare j) ≤ Real.sqrt (Real.log βhat)*
            (1+roof (d:=d) (Q:=Q) B v βhat*‖Annex.compress D p.2‖) ∧
          Published R L a depth i w p T:=by
  intro M H
  obtain ⟨school,rootsPay⟩:=WilsonOlderFreshGraphMatrixPrice.on_run simple R I d Q level law purchase
  obtain ⟨B,v,b0,submission⟩:=WilsonOlderFreshGraphSubmit.original R L a depth simple purchase.2 o w Q
  refine ⟨school,B,v,b0,?_⟩
  filter_upwards [submission,WilsonOlderFreshGraphPublication.original R L a depth simple purchase.2 o w,
    eventually_ge_atTop 1] with i incoming net late
  obtain ⟨b,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
  intro k fit hk σ βhat p
  let x:=R.alloy.B.a.clock.J (b+1)
  let K:=R.metals.p.kernel
  let a₀:=WilsonOlderFreshGraphPainter.width G K d Q x
  have radius:WilsonOlderFreshGraphRoster.narrow R d Q (b+1)=a₀:=by
    unfold a₀ K x WilsonOlderFreshGraphRoster.narrow WilsonOlderFreshGraphPainter.width
    have idK:R.family.path.levels.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
    rw [idK];rfl
  rw [radius] at incoming
  obtain ⟨t,exactBank,wage⟩:=incoming p
  let J:=WilsonOlderFreshGraphMatrixPrice.printer G I d Q level K x
  obtain ⟨reach,cap⟩:=rootsPay b k fit hk
  let T:=reprint J t d0 σ reach
  refine ⟨T,?_,?_⟩
  · have hJ:1+J.cap ≤ Real.sqrt (Real.log βhat):=Real.le_sqrt_of_sq_le cap
    have keep:=J.uniform t
    rw [wage] at keep
    have day:0 ≤ 1+roof (d:=d) (Q:=Q) B v βhat*‖Annex.compress D p.2‖:= by
      change 0 ≤ 1+roof B v (R.family.path.levels.clock.hatBeta (b+1))*‖Annex.compress D p.2‖
      rw [←wage];linarith [t.wage0]
    exact keep.trans (mul_le_mul_of_nonneg_right (by linarith:J.cap ≤ Real.sqrt (Real.log βhat)) day)
  · intro j n A s
    have named:=net p.1.1 p.1.2 p.2 j.val n A s
    have read:=J.reading j.val (Nat.le_of_lt_succ j.isLt) t n A s
    rw [exactBank] at read
    exact named.symm.trans (read.trans (Fin.sum_univ_eq_sum_range (fun l:ℕ=>
      ((J.emit l t).folded l j.val).table n (mingle A s)) (Q+1)).symm)
end YM.Integration.WilsonOlderFreshGraphDatedSalary
end
