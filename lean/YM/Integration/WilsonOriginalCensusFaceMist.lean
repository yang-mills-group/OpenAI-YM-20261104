import YM.Integration.WilsonNeutralTwoPrintPathCalendar

/-! Dependence of a fixed finite Wilson conditional on the genuine source
restrictions of the given occupied face, including the quiet and all its subfaces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceMist
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)


open WilsonReceivedDatedVerseReprint (printed Issued)
open WilsonReceivedCanonicalVerseTrial (result)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds

open WilsonReceivedCompactVerseEntrance (submit)
open WilsonNeutralTwoPrintPathCalendar (spent)
variable {G:Gauge}{ι:Type}[DecidableEq ι]{d:ι→ℕ}

theorem ordinary (M K:family G d)(S:Finset ι)(same:∀j,j⊆S→M j=K j):
  levelsO M S=levelsO K S:=by
  induction S using Finset.strongInductionOn
  rename_i S ih
  rw [levelsO,levelsO]
  split
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases used:j⊆S ∧ j≠∅
    · simp only [dif_pos used]
      rw [same j used.1,ih (S\j) (sh_k used.1 used.2) (fun i hi=>same i (hi.trans sdiff_subset))]
    · simp only [dif_neg used]

theorem connected {U:Type}(M K:thalamus d U)(S:Finset ι)(same:∀j,j⊆S→M j=K j):
  turnTLog M S=turnTLog K S:=by
  induction S using Finset.strongInductionOn
  rename_i S ih
  rw [turnTLog,turnTLog]
  split
  · rfl
  · rw [same S (Subset.rfl)]
    apply congrArg (fun H:Layers (Pen d S) U=>K S-(S.card:ℝ)⁻¹ • H)
    apply Finset.sum_congr rfl
    intro j _
    by_cases used:j⊆S ∧ j≠S
    · simp only [dif_pos used]
      rw [ih j (lt_of_le_of_ne used.1 used.2) (fun i hi=>same i (hi.trans used.1)),
        same (S\j) sdiff_subset]
    · simp only [dif_neg used]

theorem relative {c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (U:Matrix (Body 1 f) (Body 1 c) ℝ)(κ:ChartRatio G)(W:PChart G f)
    (M K:family G d)(t:Cost)(k:ι→ℕ)(s:Finset ι)(same:∀j,j⊆s→M j=K j):
    WilsonCoeffUV.Wheel.Mark.mist S F H U κ W M t k s=WilsonCoeffUV.Wheel.Mark.mist S F H U κ W K t k s:=by
  have agree:inHeat S F H U κ W M s=inHeat S F H U κ W K s:=
    connected _ _ s (fun j hj=>congrArg (fun v:Era G (Pen d j)=>srShade S F H U κ W (v.1 f))
      (ordinary M K j (fun i hi=>same i (hi.trans hj))))
  unfold WilsonCoeffUV.Wheel.Mark.mist
  rw [agree]

theorem response [Fintype ι] (R:Run G)(k:ι→ℕ)(N j e:ℕ)(n:Side)(Y:Outerm G d)
    (filed:Wellness k (submit Y k e))(a b:ι → Cover)
    (digit:ι→Site (loose R.family.path.levels j).L)(s:Finset ι)
    (within:∀v∈s,a v=b v):spent R k N j e n Y a digit s=spent R k N j e n Y b digit s:=by
  unfold spent
  apply relative
  intro j hj
  exact filed.filial _ _ j (fun v hv=>by dsimp [chartIn];rw [within v (hj hv)])

end YM.Integration.WilsonOriginalCensusFaceMist
end
