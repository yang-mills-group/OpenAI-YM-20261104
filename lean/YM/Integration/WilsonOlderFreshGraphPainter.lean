import YM.Integration.WilsonOlderFreshGraphRoster

/-! The native Ward-to-curvature renderer for the independently computed
normalized column. One publication serves all upper cutoffs and test films.
This isolates the nonlinear Ward identity of this precise filed polynomial. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphPainter
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

abbrev Ballot (i D:ℕ):= {N:ℕ // i≤N} × Studio D

def sheet (i:ℕ) (w:Letter (R.family.labels.level d)) (j:ℕ) (p:Ballot i D) :=
  WilsonOlderFreshGraphRoster.row R L a depth p.1.1 i w p.2 j

def test (i D:ℕ) (p:Ballot i D):ℝ:=‖Annex.compress D p.2‖

def width (G:Gauge) (K:KernelChoices) (d Q x:ℕ):ℝ:=
  (windowBasis G K).width x / ((d:ℝ)+Q+1)

def menu (G:Gauge) (I:Unit→Loan) (d Q:ℕ):Menu where
  width:=fun _ _ K _ x=>Agenda.path (width G K d Q x) I {()} Q (Q+1)
  positive:=fun _ _ K _ x=>Agenda.solid {()} I Q
    (div_pos ((windowBasis G K).pos x) (by positivity)) (Q+1)
  shell:=fun _=>1
  cost:=fun _=>zero_lt_one

theorem before_period {φ:ℕ→ℕ} (I:Unit→Loan) (d Q:ℕ) (law:VowsR.LawScroll G φ) (U:ℕ→ℕ)
    (before:∀(s:Sheet G)(q:MapPrices),WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s q)):
    AllPrices (Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q) simple law)
      (@WilsonWindowFormalPurchase.Canonical G U)):=fun s q=>
  joint (WilsonOlderFreshGraphSchool.before_period (menu G I d Q) simple law before s q)
    (WilsonWindowFormalPurchase.prepaid U s _)

include simple in
theorem original {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)) (I:Unit→Loan) (toll:d≤(I ()).toll) (Q:ℕ):
    ∀ᶠ i:ℕ in atTop,
      (∀(n:Side)(s:Board Unit n ℝ)(j:ℕ),j≤Q→∀p:Ballot i D,
        Haiku.Vernal G n (fun j z=>(sheet R L a depth i w j p).table n (mingle z s)) j) →
      ∃ P:ℕ→Ballot i D→Poetry.Roll G Unit,
        Agenda.Shelled {()} () I (sheet R L a depth i w) P (test i D) 1 (Q+1)
          (Agenda.path (WilsonOlderFreshGraphRoster.narrow R d Q i) I {()} Q (Q+1)) := by
  obtain ⟨B,v,nonneg,selected⟩:=WilsonOlderFreshGraphRoster.salary R L a depth simple purchase o w Q
  filter_upwards [selected] with i enroll
  intro vernal
  let b:=WilsonOlderFreshGraphRoster.narrow R d Q i
  have positive:0<b:=div_pos ((windowBasis G R.family.path.levels.clock.kernel).pos _) (by positivity)
  haveI : Nonempty (Ballot i D):=⟨(⟨i,le_rfl⟩,0)⟩
  apply Agenda.volume {()} () I (sheet R L a depth i w) (a:=b) (by
    refine ⟨positive,?_,?_,vernal⟩
    · intro j hj
      let rent (r:Fin (d+j+1)):=B (r.castLE (by omega)) *
        ageZ (R.family.path.levels.clock.hatBeta i)^(v (r.castLE (by omega)))
      have h0:0≤∑r,rent r:=Finset.sum_nonneg fun r _=>mul_nonneg (nonneg _) (by
        exact pow_nonneg (zero_le_one.trans (progZ ((WilsonWindowFormalAnnouncement.on_run R purchase).power.beta i))) _)
      refine ⟨fun p=>(∑r,rent r)*test i D p,⟨_,h0,fun p=>⟨mul_nonneg h0 (norm_nonneg _),?_⟩⟩,?_⟩
      · rw [pow_one,abs_of_nonneg (show 0≤test i D p from norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (by linarith) h0
      · intro p
        have h:=(enroll p.1.1 p.1.2 p.2 j hj).1
        dsimp [sheet]; rw [Finset.sum_mul]
        apply h.debt le_rfl le_rfl
        simp only [plusK,Finset.sum_singleton]
        omega
    · intro j hj p
      exact (enroll p.1.1 p.1.2 p.2 j hj).2) (by simp)

end YM.Integration.WilsonOlderFreshGraphPainter
end
