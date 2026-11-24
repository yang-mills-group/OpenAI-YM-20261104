import YM.Integration.NativePhysicalFieldHorizon
import YM.Integration.NativeFormalFieldTransition

/-! The finite re-scheme commutes with the original horizon inclusions
and so does its action on the full independently normalized Wilson panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalHorizonTransport

open Function Labels Lattice PhysicalNext.Repeat.Legato FVA2 FVA2.Verne
open MS MS.Local.Physical MS.Menus MS.Land FVA2.ColorCode FVA2.ArchTurn
open RegulatorIR.FVAAlt2.Moving FormalOPE.RG10.Position
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativePhysicalFieldMatrix
open NativePhysicalFieldHorizon RG11.Jets RG11.Horizon
open scoped Classical

variable {G : Gauge} {R : Run G} {hG : G.Simple} {d H : ℕ}

private theorem weights {B : MS.Local.Physical.Deck G} (e : nativeDeck R = B)
    {A : Booked B} {M : MS_Data G A} {P : Prescription B} (hm : MovingOn R e A M P)
    (μ : ℝ) (h : d ≤ H) :
    let X : Data (nativeDeck R) := e.symm ▸ (⟨A,M⟩ : Data B)
    take (includeDeck R.family.labels h) (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ X.2 H) =
      YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ X.2 d := by
  subst B
  obtain ⟨_, _, he⟩ := hm
  exact (he.apply_M μ).tower h

theorem moving (W : Bank R hG) (μ : ℝ) (h : d ≤ H) :
    restrict (includeDeck R.family.labels h) (NativeFormalFieldTransition.moving W μ H) =
      NativeFormalFieldTransition.moving W μ d := by
  refine Change.ext rfl ?_
  obtain ⟨_, _, _, _, _, _, _, hm⟩ := W.accepted
  exact weights (NativeFormalDeckAgreement.moving_deck R) hm μ h

/-- The same transfer is obtained from the smaller physical field window. -/
theorem relative (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (h : d ≤ H) :
    restrict (includeDeck R.family.labels h) (NativeFormalFieldTransition.relative W μ p H) =
      NativeFormalFieldTransition.relative W μ p d := by
  unfold NativeFormalFieldTransition.relative
  rw [NativePhysicalFieldHorizon.compose _ _ _ (NativeFormalFieldTransition.moving_good W μ H),
    moving W μ h]
  exact congrArg (Change.compose (NativeFormalFieldTransition.moving W μ d)) (inverse (warehouse R) p h)

private theorem raises (F : Frames G) (h : d ≤ H) (a : FormalOPE.RG10.Position.Deck F d) :
    RG11.Fields.up F h ((deck F d) a) = (deck F H) (includeDeck F h a) := by
  change RG11.Fields.up F h ((deck F d) a) = (deck F H) (Deck.climb F h a)
  apply Extra.FD.writes_inj F H
  rw [RG11.Fields.up_write, ← cabin F h a, writes_higher]

private theorem selected_series (V : Warehouse G) {D : Booked (wings G)} (M : MS_Data G D)
    (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG M J)
    (h : d ≤ H) :
    slice (includeDeck V.F h) (series (Forge.Check V M J μ X) H) =
      series (Forge.Check V M J μ X) d := by
  funext v
  apply PowerSeries.ext
  intro n
  let P := Forge.Check V M J μ X
  have he := (OPEPanelAction.wilsonReport V M J μ X).packs d H v.1.n n h v.1.test (deck V.F d ∘ v.2)
  change P.lives d n v.1.n v.1.test (deck V.F d ∘ v.2) =
    P.lives H n v.1.n v.1.test (RG11.Fields.up V.F h ∘ (deck V.F d ∘ v.2)) at he
  have hv : RG11.Fields.up V.F h ∘ (deck V.F d ∘ v.2) =
      deck V.F H ∘ (view (includeDeck V.F h) v).2 :=
    funext fun i => raises V.F h (v.2 i)
  change PowerSeries.coeff n (series P H (view (includeDeck V.F h) v)) = PowerSeries.coeff n (series P d v)
  rw [series, PowerSeries.coeff_mk, series, PowerSeries.coeff_mk]
  exact (he.trans (congrArg (P.lives H n v.1.n v.1.test) hv)).symm

/-- Recalibrating the true Wilson panel, then restricting all its inputs,
gives its recalibration in the original smaller field window. -/
theorem selected (W : Bank R hG) (μ : ℝ) {k : ℝ}
    (J : PositionX.Bend.Booth k (warehouse R).F) (X : Pic.pass (warehouse R) hG W.data J)
    (h : d ≤ H) :
    let p := Forge.transfer (warehouse R) W.data J μ X
    let P := Forge.Check (warehouse R) W.data J μ X
    slice (includeDeck R.family.labels h) ((toComplex (NativeFormalFieldTransition.relative W μ p H)).act
      (series P H)) = (toComplex (NativeFormalFieldTransition.relative W μ p d)).act (series P d) := by
  dsimp only
  let p := Forge.transfer (warehouse R) W.data J μ X
  have hz : Held (includeDeck R.family.labels h) (toComplex (NativeFormalFieldTransition.relative W μ p H)).Z := by
    intro a b hb
    change deposit ((NativeFormalFieldTransition.relative W μ p H).Z (includeDeck R.family.labels h a) b) = 0
    rw [Coherent.allHeld _ (coherent R.family.labels h) (NativeFormalFieldTransition.relative_good W μ p H).field a b hb,
      map_zero]
  have hr : restrict (includeDeck R.family.labels h) (toComplex (NativeFormalFieldTransition.relative W μ p H)) =
      toComplex (NativeFormalFieldTransition.relative W μ p d) :=
    congrArg toComplex (relative W μ p h)
  have hs : slice (includeDeck R.family.labels h) (series (Forge.Check (warehouse R) W.data J μ X) H) =
      series (Forge.Check (warehouse R) W.data J μ X) d := selected_series (warehouse R) W.data μ J X h
  rw [slice_action _ hz, hr, hs]

end YM.Integration.NativeFormalHorizonTransport
end
