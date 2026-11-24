import YM.Integration.NativeFormalCouplingTransition
import YM.Integration.NativePhysicalFieldMatrix

/-! The finite coupling and field re-scheme from the actual selected
position-normalized Wilson panel to the funded moving regulator target. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalFieldTransition

open Lattice Labels PhysicalNext.Repeat.Legato FVA2 FVA2.Verne
open MS MS.Local.Physical MS.Menus MS.Land FVA2.ColorCode FVA2.ArchTurn
open RegulatorIR.FVAAlt2.Moving FormalOPE.RG10.Carryon
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativePhysicalFieldMatrix
open RG11.Jets PowerSeries
open scoped Classical

variable {G : Gauge} {R : Run G} {hG : G.Simple}
local notation "I" d => FormalOPE.RG10.Position.Deck R.family.labels d

private theorem stored_weight {D : Deck G} (e : nativeDeck R = D) {A : Booked D}
    {M : MS_Data G A} {P : Prescription D} (h : MovingOn R e A M P) (μ : ℝ) (d : ℕ) :
    YM.FVAAlt2.Mass.Weight (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ
      (e.symm ▸ (⟨A, M⟩ : Data D) : Data (nativeDeck R)).2 d) := by
  subst D
  obtain ⟨_, _, hM⟩ := h
  exact ((hM.apply_M μ).funds d).2

/-- The moving change is the purchased inverse convention and the original
regulator's normalized matrix, at the same scale and field horizon. -/
def moving (W : Bank R hG) (μ : ℝ) (d : ℕ) : Change ℝ (I d) :=
  ⟨(W.convention μ).refund.x, YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d⟩

theorem moving_good (W : Bank R hG) (μ : ℝ) (d : ℕ) :
    Change.Good (allowance R.family.labels d) (moving W μ d) := by
  have hw : YM.FVAAlt2.Mass.Weight (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d) := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := W.accepted
    exact stored_weight (NativeFormalDeckAgreement.moving_deck R) h μ d
  refine ⟨⟨(W.convention μ).refund.atOrigin, ?_⟩, ⟨?_, ?_⟩⟩
  · change IsUnit (coeff 1 (W.convention μ).refund.x)
    rw [NativeFormalCouplingTransition.refund_primary _ (NativeFormalCouplingTransition.purchased_primary W μ)]
    exact isUnit_one
  · exact hw.zeroA
  · intro k _ i j hij
    change coeff k (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d i j) = 0
    rw [hw.off_bill i j hij, map_zero]

def relative (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (d : ℕ) : Change ℝ (I d) :=
  Change.compose (moving W μ d) (Change.undo (scheme p d) (good p d))

/-- The relative group action has the independently computed native
coupling coordinate, at every field horizon. -/
theorem coupling (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (d : ℕ) :
    (relative W μ p d).g = (NativeFormalCouplingTransition.transition W μ p).x := by
  have hu : IsUnit (coeff 1 (mk p.f)) := by
    rw [coeff_mk, p.primary]
    exact isUnit_one
  change PowerSeries.subst (W.convention μ).refund.x (reverse (mk p.f) (good p d).ruler) =
    (W.convention μ).refund.charge (NativeFormalCouplingTransition.physical p).refund.x
  rw [Warp.turning]
  apply congrArg (PowerSeries.subst (W.convention μ).refund.x)
  change (mk p.f).substInvOfIsUnit hu = PertExtension.Position.Triangle.inverseScale (mk p.f)
  rw [PertExtension.Position.Triangle.inverseScale, dif_pos hu]

theorem relative_good (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (d : ℕ) :
    Change.Good (allowance R.family.labels d) (relative W μ p d) :=
  (moving_good W μ d).compose (Change.Good.undoes _ (good p d))

/-- Neither a field beyond the input horizon nor a higher perturbative
coefficient is needed to transport a finite physical measurement. -/
theorem finite (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (d n : ℕ)
    {a b : Datum R.family.labels d → PowerSeries ℝ} (v : Datum R.family.labels d)
    (he : ∀ w, Through n (a ⟨v.1,w⟩) (b ⟨v.1,w⟩)) :
    Through n ((relative W μ p d).act a v) ((relative W μ p d).act b v) :=
  (Change.EquivJet.refl (c := relative W μ p d)).act (relative_good W μ p d).ruler.base he

theorem roundtrip (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) (d : ℕ)
    (a : Datum R.family.labels d → PowerSeries ℝ) :
    (Change.undo (relative W μ p d) (relative_good W μ p d)).act ((relative W μ p d).act a) = a ∧
      (relative W μ p d).act ((Change.undo (relative W μ p d) (relative_good W μ p d)).act a) = a :=
  ⟨Change.undo_action_left _ _ _, Change.undo_action_right _ _ _⟩

private theorem component_transport (L : ℂ →ₗ[ℝ] ℝ) (W : Bank R hG) (μ : ℝ)
    (P : Panel R.family.labels) (hP : P.clearP) (p : Hop R.family.labels) (d : ℕ) :
    (relative W μ p d).act (fun u => part L (series (Hop.act P p) d u)) =
      (moving W μ d).act (fun u => part L (series P d u)) := by
  rw [funext (component_action L P hP p d), relative, ← Change.act_act _ _
    (moving_good W μ d).ruler.base (Change.Good.undoes _ (good p d)).ruler.base,
    Change.undo_action_left]

/-- The full complex reading agrees, including independent phases of the
test and all tensor insertions in the original RG10 detector. -/
theorem complex_transport (W : Bank R hG) (μ : ℝ) (P : Panel R.family.labels)
    (hP : P.clearP) (p : Hop R.family.labels) (d : ℕ) (v : Datum R.family.labels d) :
    (toComplex (relative W μ p d)).act (series (Hop.act P p) d) v =
      (toComplex (moving W μ d)).act (series P d) v := by
  apply split_parts
  · rw [← part_transform real _ _ (relative_good W μ p d).ruler.base,
      ← part_transform real _ _ (moving_good W μ d).ruler.base]
    exact congrFun (component_transport real W μ P hP p d) v
  · rw [← part_transform imag _ _ (relative_good W μ p d).ruler.base,
      ← part_transform imag _ _ (moving_good W μ d).ruler.base]
    exact congrFun (component_transport imag W μ P hP p d) v

/-- The input is precisely the physical Wilson panel selected by the
three-point receiver in this economy. -/
theorem selected (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (d : ℕ) (v : Datum R.family.labels d) :
    (toComplex (relative W μ (Forge.transfer (warehouse R) W.data J μ X) d)).act
        (series (Forge.Check (warehouse R) W.data J μ X) d) v =
      (toComplex (moving W μ d)).act (series (Pic.marked (warehouse R) W.data μ) d) v := by
  rw [Forge.agrees]
  exact complex_transport W μ (Pic.marked (warehouse R) W.data μ)
    (Pic.clearMark (warehouse R) W.data μ) (Forge.transfer (warehouse R) W.data J μ X) d v

private theorem original_readout (W : Bank R hG) (μ : ℝ) (d : ℕ) (v : Datum R.family.labels d) :
    part real (series (Pic.marked (warehouse R) W.data μ) d v) =
      NativeFormalDetectorReadings.panel R rfl W.data μ d v := by
  apply PowerSeries.ext
  intro k
  rw [component, series, coeff_mk]
  have he := congrArg Complex.re (W.panel μ d k v)
  rw [W.report] at he
  exact he

def Reconstructs (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) : Prop :=
  ∀ d : ℕ, ∀ v : Datum R.family.labels d,
    part real ((toComplex (relative W μ (Forge.transfer (warehouse R) W.data J μ X) d)).act
        (series (Forge.Check (warehouse R) W.data J μ X) d) v) =
      YM.FVAAlt2.Home.mix ((YM.FVAAlt2.Convert.f (Study.Plan R) μ W.native.2).charge ∘
        YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels d)
        (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d) v

/-- The right side is the original regulator target on this same family. -/
theorem regulated (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) : Reconstructs W μ J X := by
  intro d v
  rw [selected W μ J X d v, ← part_transform real _ _ (moving_good W μ d).ruler.base,
    W.coupling, W.report]
  simp_rw [original_readout W μ d]
  change YM.FVAAlt2.Home.mix (fun z => subst (W.convention μ).refund.x
    (NativeFormalDetectorReadings.panel R rfl W.data μ d z)) _ v = _
  exact congrArg (fun f => YM.FVAAlt2.Home.mix f
    (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d) v)
    (funext fun z => (Warp.turning (W.convention μ).refund
      (NativeFormalDetectorReadings.panel R rfl W.data μ d z)).symm)

/-- A single original purchase supplies the physical and moving
identifications and the full finite regulator transport at each scale. -/
theorem paid (W : Bank R hG) (μ : ℝ) :
    let V := warehouse R
    ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
      (k : ℝ) (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG W.data J),
      Atoll.Main.Economy hG V W.book W.data P S U J ∧
      MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book V) W.data P ∧
      Reconstructs W μ J X := by
  obtain ⟨P, S, U, k, J, _, H, h⟩ := W.accepted
  obtain ⟨X, _⟩ := H.hymns μ
  exact ⟨P, S, U, k, J, X, H, h, regulated W μ J X⟩

end YM.Integration.NativeFormalFieldTransition
end
