import YM.Integration.NativeFormalPrescriptionAgreement
import YM.Integration.WilsonCoefficientPreparation

/-! The moving and fixed-regulator formal suppliers use one physical deck,
the same MS field data and the same complete series of coupling and gauge counterterms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalSharedCoupling

open Lattice Labels PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Land MS.Menus MS.Book MS.Book.Program MS.Outlook
open MS.High MS.High.Knobs MS.Wind MS.Wind.Leading MS.Mach MS.Lifting
open YM.FVA2 YM.FVA2.ColorCode YM.FVA2.ArchTurn
open NativeFormalPrescriptionAgreement

variable {G : Gauge}

/-- The formal bulk calibration depends on the full series of counterterms. -/
def Bulk {B : Deck G} {A : Booked B} (M : MS_Data G A) (p : Team) : Prop :=
  Fixed (col (skyline G p)) (Archive 4 M.bulk) true 4 1

theorem moving_bulk (R : Run G) {B : Deck G} (e : nativeDeck R = B)
    {A : Booked B} {M : MS_Data G A} {T : Land.Prescription B}
    (h : MovingOn R e A M T) : Bulk M T.team := by
  subst B
  obtain ⟨_, _, hm⟩ := h
  exact (hm.apply_M 0).draw.high.bulk

/-- The native marked-linear solver works for the specified bulk team
on every field in the book. -/
theorem profile_with_team {B : Deck G} {A : Booked B} (M : MS_Data G A)
    (V : YM.FVA2.Source.NativeDictionary B) (hG : G.Simple) (p : Team) (h : Bulk M p) :
    ∃ Q : Prescription B, Matched.AllProfiles M V Q ∧ Q.team = p := by
  have fields d (i : Plaid B d) :=
    physicalAt V.book (j := Land.read i) hG h
      (MS.Outlook.fieldD M.bulkOK (M.markOK d i) MS.Motif.wisdom ((A.law d i).moodQ))
      (initialHF (A.law d i) (sizeG i) (M.markOK d i))
  choose S hs hS using fields
  let Q : Prescription B := ⟨p, S, hs⟩
  have ht : TaylorOK M V.book Q := ⟨h, hS⟩
  exact ⟨Q, ⟨ht, fun _ _ _ X μ w l hX => Matched.clears M V X Q μ w l hX hG ht⟩, rfl⟩

abbrev warehouse (R : Run G) :=
  Atoll.share R.family R.makes (CoefficientBridge.run_valuation R)

/-- The full moving correlation, all direct finite-geometry profiles, and
the averaged FVA2 formal coefficient prescription on the same warehouse. -/
def Shared (R : Run G) (hG : G.Simple) : Prop :=
  let V := warehouse R
  ∃ (B : Booked (wings G)) (A : MS_Data G (angular B V)) (T Q P : Prescription (wings G)),
    RadL.Reg B ∧ MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B V) A T ∧
    Matched.AllProfiles A (V.diction (wings G)) Q ∧ Q.team = T.team ∧
    ∃ (E : Blaze.ExactSpin V P) (U : Frost.Trusted P) (k : ℝ) (J : _),
      Atoll.Main.Economy hG V B A P E U (t := k) J ∧ P.team = T.team

theorem shared (R : Run G) (hG : G.Simple)
    (hWindow : NativeFVAPlateau.Funded R.family.path.levels) : Shared R hG := by
  let V := warehouse R
  obtain ⟨B, hB⟩ := MS.RadL.picks (wings G)
  let A := Classical.choice (bookedMS (angular B V))
  obtain ⟨T, hT⟩ := moving_on_angular R hG hWindow B V rfl A
  obtain ⟨Q, hQ, hQT⟩ := profile_with_team A (V.diction (wings G)) hG T.team
    (moving_bulk R (NativeFormalDeckAgreement.moving_deck R) hT)
  obtain ⟨P, E, U, k, J, hE, hPQ⟩ :=
    Atoll.Main.accounts hG V B A Q hQ (MS.RadL.radial V hB)
  exact ⟨B, A, T, Q, P, hB, hT, hQ, hQT, E, U, k, J, hE, hPQ.trans hQT⟩

end YM.Integration.NativeFormalSharedCoupling
end
