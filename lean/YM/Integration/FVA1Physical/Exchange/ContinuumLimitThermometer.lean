import YM.FVA2.XReg.Choice
import YM.WilsonMS.Scales.Stance

/-! Equality of the two independent *formal* connected detector series at a common
reference scale and on one filed Rose test. The equality does not use an estimate
for a finite positive-coupling detector or identify the two finite quadratures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange
open Function Filter XSpace XSpace.Normalize XSpace.Cirrus
open MS MS.Local.Physical MS.Menus MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open MS.High MS.High.Knobs MS.Outlook MS.Wind MS.Wind.Leading MS.Motif MS.Mach MS.Dock MS.Hem
open FVA2 FVA2.Position WilsonMS
open scoped Topology Classical
variable {G : Gauge}

/-- The nonnegative clamp in the independent cutoff clock disappears on the
same refining, expanding Front used by the filed detector. -/
theorem continuumLimit_reset (μ : ℝ) (S : Prescription (Press.portDeck G))
    (A : Prescription (Ensure.deck G)) (team : S.team = A.team) :
    ∀ᶠ m in Front, Dframe.reset μ S m = FrameConj.pι A μ m := by
  filter_upwards [frontier.smaller] with m hm
  change Program.shift S.team (μ - max (-Real.log m.spacing) 0) =
    Program.shift A.team (μ - (-Real.log m.spacing))
  rw [team, max_eq_left (neg_nonneg.mpr (Real.log_nonpos m.positive.le hm))]

/-- Exact agreement under possibly different marked fee schedules after the
common bulk coupling has been chosen. Both series converge coefficientwise
from the same finite Rose detector reading after its triangular reset. -/
theorem continuumLimit_detector_of_team (μ : ℝ) {V : Store G} (P : Rose.Pick V)
    (W : Initialize G) (S : Prescription (Press.portDeck G)) (A : Prescription (Ensure.deck G))
    {O : Booked (Press.portDeck G)} (T : MS_Data G O)
    {M : Booked (Ensure.deck G)} (F : MS_Data G M) (h : G.Simple)
    (hs : TaylorOKF T (Press.wickInput W) S) (hr : Favors.Horder S) (hv : Ace.UnitP S)
    (ha : BMenu.Installed W F A) (hc : Rider.Commuting A) (team : S.team = A.team) :
    FVA2.Reg.Choice.choice μ P T = FrameConj.χMS μ P F := by
  apply PowerSeries.ext
  intro j
  apply tendsto_nhds_unique _ (FrameConj.tracked μ P W A F h ha hc j).limit
  apply (FVA2.Reg.Choice.forecast μ W P S T h hs hr hv j).congr'
  filter_upwards [continuumLimit_reset μ S A team] with m hm
  change PowerSeries.coeff j ((Rose.chosen W P m).subst (Dframe.reset μ S m)) =
    PowerSeries.coeff j ((Rose.chosen W P m).subst (FrameConj.pι A μ m))
  rw [hm]

/-- The bulk archive has no marked optics. The common MS interaction and pole
conditions identify it even when the two books have different field labels. -/
theorem continuumLimit_ms_bulk {D E : Deck G} {O : Booked D} {M : Booked E}
    (X : MS_Data G O) (F : MS_Data G M) : Archive 4 X.bulk = Archive 4 F.bulk := by
  obtain ⟨_, hp⟩ := unique_B X.bulkOK F.bulkOK
  exact funext fun n => funext fun z =>
    HBeam.four_pact (gang (X.bulkOK n)).dost (gang (F.bulkOK n)).dost (hp n) z

/-- Fund all marked rows on the *specified* bulk team; the orientation average
and exact unit-column repair preserve that chosen team. -/
theorem continuumLimit_fund_team (W : Initialize G) (T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (h : G.Simple) (q : Team) (hq : Fixed (col (skyline G q)) (Archive 4 T.bulk) true 4 1) :
    ∃ S : Prescription (Press.portDeck G), S.team = q ∧ Ace.Sag W T S := by
  let V := Press.wickInput W
  let O := OpenAxis.Plot (Press.portDeck G)
  have he (d : ℕ) (i : Plaid (Press.portDeck G) d) :=
    physicalAtF V (j := Land.read i) h hq
      (Outlook.fieldD T.bulkOK (T.markOK d i) wisdom ((O.law d i).moodQ))
      (initialHF (O.law d i) (sizeG i) (T.markOK d i))
  choose b hfit hmark using he
  let A : Prescription (Press.portDeck G) := ⟨q, b, hfit⟩
  have hA : TaylorOKF T V A := ⟨hq, hmark⟩
  obtain ⟨hx, hs⟩ := Favors.upgrades W T A hA
  exact ⟨Ace.amen (Favors.Norm₀ A), rfl, Ace.correct W T _ hx, Ace.strictU _ hs, Ace.horiz _⟩

/-- At *every* order the canonical ContinuumLimit formal coupling detector is the filed
WilsonMS detector. No agreement of marked continuations, cutoff measurements
or teams is assumed. Both MS inputs carry their original defining laws. -/
theorem continuumLimit_filed_detector (μ : ℝ) {V : Store G} (P : Rose.Pick V)
    (T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (F : MS_Data G (JRad.book G)) (h : G.Simple) :
    FVA2.Reg.Choice.choice μ P T = FrameConj.χMS μ P F := by
  let W := Initialize.standard G
  obtain ⟨A, hc, ha⟩ := Rider.Equipped W F h
  have hb : Fixed (col (skyline G A.team)) (Archive 4 T.bulk) true 4 1 := by
    rw [← continuumLimit_ms_bulk F T]
    exact ha.bulk
  obtain ⟨S, ht, hs⟩ := continuumLimit_fund_team W T h A.team hb
  exact continuumLimit_detector_of_team μ P W S A T F h hs.Taylor hs.still hs.base ha hc ht

end YM.Integration.FVA1Physical.Exchange
