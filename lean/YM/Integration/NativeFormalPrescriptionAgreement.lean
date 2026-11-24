import YM.Integration.NativeFormalDeckAgreement
import YM.FVA2.Deliver

/-! The moving and FVA2 formal correlation suppliers can use one set of
dimensionally continued MS field data on one original Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalPrescriptionAgreement

open Lattice Labels Precision RG RegulatorIR PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Land
open YM.FVAAlt2 YM.FVA2.ColorCode
open RegulatorIR.FVAAlt2.Moving

variable {G : Gauge}

theorem turn (s : Signed) :
    MS.FVA.Motions.turnBo G s = YM.FVA2.ArchTurn.polar (G := G) s⁻¹ := rfl

/-- Both rotations read the same coefficient in the same physical field basis. -/
theorem coordinate (F : Frames G) (s : Signed) (d : ℕ) (i j : Plaid (wings G) d) :
    Home.localStep F (wings G) d s i j = (fee F s.ortho d i j : ℂ) :=
  (held_real F s.ortho d (Land.read i) (Land.read j)).symm

/-- The signed covariance of the averaged radially admissible FVA2 book
is exactly the covariance used in the moving launch. -/
theorem angular_spect (B : Booked (wings G)) (V : YM.FVA2.Warehouse G) :
    Convert.Spect V.F (YM.FVA2.ArchTurn.angular B V) := by
  intro s d i
  simpa only [turn, coordinate] using YM.FVA2.ArchTurn.lit B V s i

abbrev nativeDeck (R : Run G) :=
  Home.seats (Study.Plan R).liftOff (Study.Plan R).certified

/-- The moving supplier uses this specific book, MS data and prescription,
transported along literal equality of decks. -/
def MovingOn (R : Run G) {B : Deck G} (hB : nativeDeck R = B)
    (A : Booked B) (H : MS_Data G A) (T : Prescription B) : Prop := by
  subst B
  exact ∃ (Z : ∀ p : Patch, p.Branches R.family.path.levels.clock.kernel G)
    (C : RegulatorIR.FVAAlt2.Lodge.Contract R (Oracle.books R.family.path.levels.clock.kernel) Z),
    Supplier.CorrelationMatch (Oracle.books R.family.path.levels.clock.kernel) Z R C H T

/-- The full moving comparison can be run with a supplied covariant book
and its specified MS data, using precisely this Run's regulator window. -/
theorem moving_of_spect (R : Run G) (hG : G.Simple) (hWindow : NativeFVAPlateau.Funded R.family.path.levels)
    {B : Deck G} (hB : nativeDeck R = B) (A : Booked B) (M : MS_Data G A)
    (hSpect : Convert.Spect R.family.labels A) :
    ∃ T : Prescription B, MovingOn R hB A M T := by
  subst B
  obtain ⟨Z, C⟩ := NativeFVAPlateau.contract R hWindow
  let P := Study.Plan R
  obtain ⟨hOfficial, hLift, _⟩ := Top.admitted hG (RegulatorIR.FVAAlt2.Lodge.basisR R)
  obtain ⟨T, hT⟩ := Convert.build_L _ M hG (Convert.start P) hSpect
    (fun s t _ => Convert.preamble_H s P t)
  have hOutput (μ : ℝ) := Top.customer R.metals.O R.alloy.B.ratio P hG hOfficial hLift M T μ hT
  let p := (hOutput 0).credit Top.age
  obtain ⟨W, hW, _⟩ := (hOutput 0).tilt _ p
  exact ⟨T, Z, C, hOutput, Top.age, p, W, hW, fun _ g μ l _ _ t ht htop n hn hN =>
    Supplier.empowered (Oracle.books R.family.path.levels.clock.kernel) Z R C t ht l μ
      T p W n g hG (hOutput μ) htop hN hn hW⟩

/-- This applies to the precise MS data selected by the FVA2 packing
theorem on the same warehouse. -/
theorem moving_on_angular (R : Run G) (hG : G.Simple)
    (hWindow : NativeFVAPlateau.Funded R.family.path.levels)
    (B : Booked (wings G)) (V : YM.FVA2.Warehouse G) (hF : V.F = R.family.labels)
    (M : MS_Data G (YM.FVA2.ArchTurn.angular B V)) :
    ∃ T : Prescription (wings G),
      MovingOn R (NativeFormalDeckAgreement.moving_deck R) (YM.FVA2.ArchTurn.angular B V) M T := by
  apply moving_of_spect R hG hWindow (NativeFormalDeckAgreement.moving_deck R) _ M
  simpa only [← hF] using angular_spect B V

end YM.Integration.NativeFormalPrescriptionAgreement
end
