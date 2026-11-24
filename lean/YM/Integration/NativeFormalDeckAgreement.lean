import YM.Integration.NativeFVAPlateauCorrelation
import YM.FVA2.PhysicalDeck

/-! Both formal suppliers use the closest free-equation representative
in each nonnegative weight and rank on the original Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalDeckAgreement

open Lattice Labels Maxwell Pert Pert.RawLabels Pert.Position PositionX
open MS MS.Local.Physical MS.Theater MS.Landau.Detect
open YM.FVAAlt2 YM.FVA2.ColorCode
open PhysicalNext.Repeat.Legato
open scoped Classical

variable {G : Gauge}

/-- The projection used by the moving loft is the common fixed-polynomial map. -/
theorem projector (F : Frames G) (d : ℕ) (p : Label G d) :
    Home.projector (Home.LoftPP F) d p = fixedPolynomial G d p :=
  embed_round F p

/-- Fixed polynomials and the image of the idempotent give the same graded
subspace of real laws. -/
theorem soundly_eq_rotor (F : Frames G) (d r : ℕ) :
    Home.Soundly (Home.LoftPP F) d r = rotor G d r := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have h := (Home.sunrise (Home.LoftPP F) x).mp hx
    rw [projector] at h
    have hfixed : changed (rebase G) x.val = x.val := congrArg Subtype.val h
    refine ⟨changed (rebase G) x.val, ⟨x.val, x.property, rfl⟩, ?_⟩
    change Theater.orbit G (changed (rebase G) x.val) = Theater.orbit G x.val
    rw [hfixed]
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨⟨changed (rebase G) p, activeM hp⟩, ?_, rfl⟩
    apply (Home.sunrise (Home.LoftPP F) _).mpr
    rw [projector]
    apply Subtype.ext
    exact flat_idem p

private theorem deck_ext {B D : Deck G} (h : B.carries = D.carries) : B = D := by
  cases B
  cases D
  cases h
  rfl

/-- The two real subspace families agree also at negative engineering weight. -/
theorem seats_eq_wings (F : Frames G) :
    Home.seats (Home.LoftPP F) (Home.readyPP (F := F)) = wings G := by
  apply deck_ext
  funext d r
  cases d with
  | ofNat d => simpa only [Home.seats, wings, Int.ofNat_eq_natCast,
      Int.natCast_nonneg, if_true, Int.toNat_natCast] using soundly_eq_rotor F d r
  | negSucc d => simp [Home.seats, wings]

/-- One physical deck underlies the two formal suppliers of this Run. -/
theorem moving_deck (R : Run G) :
    Home.seats (RegulatorIR.FVAAlt2.Moving.Study.Plan R).liftOff
      (RegulatorIR.FVAAlt2.Moving.Study.Plan R).certified = wings G :=
  seats_eq_wings R.family.labels

end YM.Integration.NativeFormalDeckAgreement
end
