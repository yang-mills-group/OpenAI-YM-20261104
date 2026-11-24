import YM.Integration.NativeFormalMixedProfiles
import YM.Integration.NativeFormalAngularPermit

/-! The original FVA2 economy and its physical transfer run on exactly the
moving regulator prescription, including all marked field and coupling coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalEconomyAgreement

open Lattice Labels Precision RG RegulatorIR PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Land MS.Menus
open FVA2 FVA2.ColorCode FVA2.ArchTurn
open RegulatorIR.FVAAlt2.Moving
open NativeFormalPrescriptionAgreement NativeFormalSharedCoupling

variable {G : Gauge}

/-- A specified physical prescription with a valid moving launch retains its
own field and coupling payments through every interaction-index comparison. -/
theorem accept (R : Run G) (hG : G.Simple)
    (hWindow : NativeFVAPlateau.Funded R.family.path.levels)
    {B : Deck G} (e : nativeDeck R = B) {A : Booked B} (M : MS_Data G A)
    (P : Prescription B)
    (hL : YM.FVAAlt2.Convert.Launch
      (YM.FVAAlt2.Shop.richBook B (warehouse R).F (warehouse R).H
        (warehouse R).S (warehouse R).h (warehouse R).acts) M (F := R.family.labels) P) :
    MovingOn R e A M P := by
  subst B
  obtain ⟨Z, C⟩ := NativeFVAPlateau.contract R hWindow
  let plan := Study.Plan R
  obtain ⟨hOfficial, hLift, _⟩ := YM.FVAAlt2.Top.admitted hG (RegulatorIR.FVAAlt2.Lodge.basisR R)
  have output (μ : ℝ) := YM.FVAAlt2.Top.customer R.metals.O R.alloy.B.ratio plan hG
    hOfficial hLift M P μ hL
  let q := (output 0).credit YM.FVAAlt2.Top.age
  obtain ⟨W, hW, _⟩ := (output 0).tilt _ q
  exact ⟨Z, C, output, YM.FVAAlt2.Top.age, q, W, hW, fun _ g μ l _ _ t ht htop n hn hN =>
    Supplier.empowered (Oracle.books R.family.path.levels.clock.kernel) Z R C t ht l μ
      P q W n g hG (output μ) htop hN hn hW⟩

/-- An existing FVA2 calibration with its spin and unit normalization is
accepted unchanged by the moving correlation supplier. -/
theorem moving (R : Run G) (hG : G.Simple)
    (hWindow : NativeFVAPlateau.Funded R.family.path.levels)
    (B : Booked (wings G)) (M : MS_Data G (angular B (warehouse R)))
    (P : Prescription (wings G)) (S : Blaze.ExactSpin (warehouse R) P)
    (U : Frost.Trusted P) (hM : MixedStory.AllProfiles M (warehouse R) P) :
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B (warehouse R)) M P := by
  let V := warehouse R
  apply accept R hG hWindow _ M P
  refine ⟨angular_spect B V, (NativeFormalMixedProfiles.taylor _ (V.native _)
    (NativeFormalStencilAgreement.menu V _) M P).mpr hM.1,
    NativeFormalAngularPermit.permit V P S, ?_⟩
  intro i n hn j
  rw [U.unit i, Frost.face_p, if_neg (fun h => (Nat.ne_of_gt hn) h.2)]

/-- This applies to any already selected FVA2 Economy and its own physical
transfer, including every signed Pic pass licensed by its hymns. -/
theorem on_economy (R : Run G) (hG : G.Simple)
    (hWindow : NativeFVAPlateau.Funded R.family.path.levels)
    (B : Booked (wings G)) (M : MS_Data G (angular B (warehouse R)))
    (P : Prescription (wings G)) (S : Blaze.ExactSpin (warehouse R) P)
    (U : Frost.Trusted P) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (H : Atoll.Main.Economy hG (warehouse R) B M P S U J) :
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B (warehouse R)) M P :=
  moving R hG hWindow B M P S U H.paid.rates

/-- One original physical economy, its transfer, and the complete moving
prescription operate on the identical calibrated fields and period. -/
theorem common (R : Run G) (hG : G.Simple) (h : NativeFVAPlateau.Correlations R) :
    let V := warehouse R
    ∃ (B : Booked (wings G)) (M : MS_Data G (angular B V)) (P : Prescription (wings G))
      (S : Blaze.ExactSpin V P) (U : Frost.Trusted P) (k : ℝ) (J : _),
      RadL.Reg B ∧ Atoll.Main.Economy hG V B M P S U (t := k) J ∧
      MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B V) M P := by
  have hw := NativeFormalMixedProfiles.windows h
  obtain ⟨B, M, _, _, P, hB, _, _, _, S, U, k, J, H, _⟩ := shared R hG hw
  exact ⟨B, M, P, S, U, k, J, hB, H, on_economy R hG hw B M P S U J H⟩

/-- The original Lodge construction realizes the paid formal correlation on
one Run with any prescribed physical penalty and all its extraction finals. -/
theorem at_penalty (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Run G, R.family.path.levels.clock.kernel.penalty = ε ∧ Run.Ties R ∧
      (∀ a : Extraction.Order, ∃ (b : Extraction.Order) (T : Table R.family.book),
        Nonempty (Spec.Final R.family (a.refine b) T)) ∧ NativeFVAPlateau.Correlations R := by
  obtain ⟨K, hK, Z⟩ := Axial.viable G ε hε
  obtain ⟨R, C⟩ := RegulatorIR.FVAAlt2.Lodge.reception G hG (Oracle.books K) Z
  have hpen := (congrArg KernelChoices.penalty C.law).trans hK
  obtain ⟨hT, hF⟩ := Run.again R hG
  have e : R.family.path.levels.clock.kernel = K := C.law
  subst K
  exact ⟨R, hpen, hT, hF, NativeFVAPlateau.correlations hG R ⟨Z, C.holds⟩⟩

end YM.Integration.NativeFormalEconomyAgreement
end
