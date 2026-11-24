import YM.Integration.WilsonCapturedRegisteredSeat
import YM.Integration.WilsonPointChildCenteredPortfolio

/-! Each named film fixes its own test before the run, the two dates and both periods.
The translated covered entry is its authentic chart on every auxiliary side.
The finite entry has the original quantitative winding bill on each physical side. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedSoldSeedPanel
open Function Filter Finset Lattice Wilson RG Laurent PowerSeries Bloch WilsonCoeffUV.Cosmos
open FormalBulk08 Flat Reef Jets Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNamedBasis WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Soil
open WilsonOriginalPlacedPrimerInk WilsonPointChildCenteredFunctional
open scoped Classical Topology BigOperators ContDiff
open WilsonCapturedRegisteredSeat
variable {ι:Type}{G:Gauge}{h:ι→ℕ}

/-- The same functional is used when the same film is entered at two different dates. -/
def panel (films:∀s,Studio (h s)):Case h:=
  fun s=>page (h s) (WilsonCapturedRegisteredSeed.film (films s)).choose

theorem bounded (films:∀s,Studio (h s))(s:ι):‖panel films s‖≤‖films s‖:=
  (WilsonCapturedRegisteredSeed.film (films s)).choose_spec.2

variable (R:Run G)(simple:G.Simple)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ → Gear G → ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)

include o simple tags paid in
theorem covered (k:ι→ℕ)(depth:∀s,k s<h s)(u:ι→G.ColorIndex)
    (N j:ℕ)(live:j≤N)(up:∀s,k s≤R.family.path.levels.clock.J j)
    (digit:ι→∀i,Site (R.family.S.block i))(v:∀s,Letter (R.family.labels.level (k s)))
    (films:∀s,Studio (h s))(s:ι)(z:Cover)(n:Side)(e r:ℕ):
    let V:=panel films
    let Z:=seat R (u s) (k s) h s (depth s) (digit s) N j (v s) z
    (touch V {s}) ∘ plume (Z.2 e r) n =
      WilsonOlderFreshPointChart.chart R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s) n (wrap n z) e r:=by
  intro V Z
  let X:=issue R (u s) (k s) h s (depth s) (digit s) N j (v s)
  let Y:=WilsonOlderFreshPointGauge.field R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s)
  let tester:=touch V {s}
  let p:Scroll (h s):=(WilsonCapturedRegisteredSeed.film (films s)).choose
  have eqp:= (WilsonCapturedRegisteredSeed.film (films s)).choose_spec.1
  have law:=WilsonPointChildCenteredJet.original R (routes R) (u s) (depth s) (digit s) N j (v s) p
  change physical p=films s at eqp
  rw [eqp] at law
  have aligned:tester ∘ X.2 e r=Y e r:=by
    funext x
    exact (WilsonPointChildCenteredFunctional.original R (u s) (k s) h s (depth s) (digit s) o
      simple price paid tags N j live (up s) (v s) e r x V).trans
        (congrArg (fun t:Pot G=>t e r x) law.symm)
  have ward:=WilsonNeutralPointCourse.original R (routes R) (u s) (depth s) (digit s) N j simple o live
    ((up s).trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have shelf:=clef_through (ward.officers (v s)) (slotsFits _ (v s))
  have chart:WilsonOriginalPrimerInk.column (k s) Y n e r=plume (Y e r) n:=
    ground Y (shelf.fare.1 (films s)) (fun e r=>shelf.fare.2.1 (films s) e r) n e r
  have auth:=WilsonPointChildCenteredFunctional.authorized R simple o (u s) (k s) h s (depth s) (digit s) N j live (v s) z
  obtain ⟨w,A,hw,cork⟩:=(auth.wing e r).land
  have undo:tester ∘ Z.2 e r=revolve z (Y e r):=by
    rw [←aligned]
    dsimp only [Z]
    rw [WilsonPointChildCenteredSeat.placed]
    rfl
  change tester ∘ plume (Z.2 e r) n=fade (place (wrap n z)) (WilsonOriginalPrimerInk.column (k s) Y n e) r
  rw [←plume_map _ cork hw tester n,undo,plume_shift,WilsonCapturedRegisteredSeat.moved,chart]


open WilsonCoeffUV.Embroider.Canvas
open WilsonMarkedIndependentNormalizedScale (rate)

variable [Fintype ι]

private theorem one (films:∀s,Studio (h s))(s:ι):‖touch (panel films) {s}‖≤‖films s‖:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [hit_leaf,mul_comm]
  exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((show ‖folio (panel films) {s}‖≤‖panel films s‖ by simpa using folio_norm (J:={s}) (panel films)).trans
      (bounded films s)) (norm_nonneg _))

include o simple tags paid in
theorem original (k:ι→ℕ)(depth:∀s,k s<h s)(u:ι→G.ColorIndex)(E:ℕ)
    (finite:WilsonPointChildDigitHierarchy.Filed R):
    ∀ᶠj:ℕ in atTop,∀(N per:ℕ)(live:j≤N)(digit:ι→∀i,Site (R.family.S.block i))
      (v:∀s,Letter (R.family.labels.level (k s)))(films:∀s,Studio (h s))(s:ι)(y:ι → Cover)(e:ℕ), e≤E → ∀r x,
      let n:=R.family.side j per
      let Z:=WilsonPointChildCenteredPortfolio.bank R u depth digit N j v y {s}
      ‖touch (panel films) {s} (Z.1 n e r x)-
        WilsonOlderFreshPointChart.chart R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s) n (wrap n (y s)) e r x‖≤
        ‖films s‖*((∑t:Spring (h s),(1+WilsonPointChildCenteredSalary.bill t))*rate R.family.path.levels j per):=by
  have bought:=Filter.eventually_all.mpr (fun s=>WilsonPointChildCenteredSeat.original R (u s) (k s) E h s (depth s) o tags simple price paid finite)
  have admitted:∀ᶠj:ℕ in atTop,∀s,k s≤R.family.path.levels.clock.J j:=
    Filter.eventually_all.mpr (fun s=>R.family.path.levels.fits.deep.eventually_ge_atTop (k s))
  filter_upwards [bought,admitted] with j dated up
  intro N per live digit v films s y e he r x n Z
  let X:=seat R (u s) (k s) h s (depth s) (digit s) N j (v s) (y s)
  have native:=WilsonPointChildPlacedFamily.singleton (fun a=>seat R (u a) (k a) h a (depth a) (digit a) N j (v a) (y a)) s
  change Z=X at native
  rw [native,←congrFun (covered R simple o tags price paid k depth u N j live up digit v films s (y s) n e r) x]
  simp only [Function.comp_apply,←map_sub]
  exact ((touch (panel films) {s}).le_opNorm _).trans
    (mul_le_mul (one films s) (dated s (digit s) N per live (v s) e he r x (y s)) (norm_nonneg _) (norm_nonneg _))

end YM.Integration.WilsonCapturedSoldSeedPanel
