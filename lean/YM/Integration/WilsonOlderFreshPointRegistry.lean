import YM.Integration.WilsonOlderFreshPointIncome
import YM.Integration.WilsonOlderFreshPointChart
/-! Choose a single point catalogue for each original date, label and
film along the same actual digit sequence. The same catalogue can be
called on the two incident courses, with no change of cutoff or pupil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointRegistry
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







def Filed {Q N j:ℕ}(δ:ℝ)(digit:∀h,Site (R.family.S.block h))(up:j≤N)
    (b:Letter (R.family.labels.level d))(f:Studio D){σ:ℝ}(T:WilsonOlderFreshGraphSlate.Copy G d Q σ):Prop:=
  (∑r,T.fare r)≤R.alloy.B.a.clock.hatBeta j^δ*(1+‖f‖) ∧
    WilsonOlderFreshPointCommission.Published R L a depth j b (⟨N,up,digit⟩,f) T ∧
    WilsonOriginalPrimerStampedRay.Matched T (WilsonOlderFreshPointChart.chart R L a depth j b (⟨N,up,digit⟩,f))

include simple in
theorem original {φ U:ℕ→ℕ}(I:Unit→Loan)(Q:ℕ)(level:(I ()).toll=d)(d0:0<d)
    (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ
       (WilsonOlderFreshGraphMatrixPrice.menu G I d Q level) simple (WilsonOlderFreshGraphMatrixPrice.jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (Lambda R.family.path.levels j))
    (o:Loc G 1)(old:WilsonPointChildWidthHistory.Income R L a depth o Q){δ:ℝ}(accuracy:0<δ):
    let M:=WilsonOlderFreshGraphMatrixPrice.menu G I d Q level
    let H:=roots M simple R.metals.p R.metals.K
    (∃books,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) books) ∧
    ∃s:ℕ,∀m:ℕ,s ≤ m → ∀(N k:ℕ)(digit:∀h,Site (R.family.S.block h)),
      k ≤ R.alloy.B.a.clock.J m→1 ≤ Burn.horizon k→d≤R.alloy.B.a.clock.J (m+1)→
      let σ:=fun j=>Agenda.seed H φ (Burn.horizon k) (R.family.path.levels.clock.J j)
      ∃T:∀j:ℕ,m ≤ j → j ≤ N → Letter (R.family.labels.level d)→Studio D→WilsonOlderFreshGraphSlate.Copy G d Q (σ j),
        ∀j (lo:m≤j)(up:j≤N)(b:Letter (R.family.labels.level d))(f:Studio D),
          Filed R L a depth δ digit up b f (T j lo up b f):=by
  intro M H
  obtain ⟨ch,buy⟩:=WilsonOlderFreshPointIncome.original R L a depth simple I Q level d0 law purchase slow o old accuracy
  obtain ⟨s,funded⟩:=eventually_atTop.mp buy
  refine ⟨ch,s,?_⟩
  intro m hm N k digit room pos grade σ
  have book (j:ℕ)(lo:m≤j)(up:j≤N)(b:Letter (R.family.labels.level d))(f:Studio D):
      ∃T:WilsonOlderFreshGraphSlate.Copy G d Q (σ j),Filed R L a depth δ digit up b f T:=by
    let p:WilsonOlderFreshPointGauge.Ballot R j D:=(⟨N,up,digit⟩,f)
    obtain ⟨T,spent,read⟩:=funded j (hm.trans lo) k (room.trans (R.alloy.B.a.fits.mono lo)) pos
      (grade.trans (R.alloy.B.a.fits.mono (Nat.succ_le_succ lo))) b p
    exact ⟨T,spent,read,WilsonOlderFreshPointChart.original R L a depth j b p T read⟩
  choose t filed using book
  exact ⟨t,filed⟩

end YM.Integration.WilsonOlderFreshPointRegistry
end
