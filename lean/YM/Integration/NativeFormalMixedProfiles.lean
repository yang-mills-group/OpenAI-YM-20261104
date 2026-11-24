import YM.Integration.NativeFormalStencilAgreement
import YM.Integration.NativeFormalSharedCoupling

/-! The full moving marked prescription certifies every formal FVA2 multiscale
profile on the same physical warehouse and with the same MS data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalMixedProfiles

open Lattice Labels Precision RG RegulatorIR PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Land MS.Menus MS.Wind MS.Book.Program
open FVA2 FVA2.ColorCode FVA2.ArchTurn
open NativeFormalPrescriptionAgreement NativeFormalSharedCoupling

variable {G : Gauge}

/-- Equal physical stencil menus give identical formal marked flows. -/
theorem horizon {B : Deck G} (X : RichBook B) (Y : BookM B)
    (menus : ∀ d r u, X.menu d r u = Y.inkM d r u)
    (p : Team) {d : ℕ} (A : Acts B d) : horizonPl X p A = horizonM Y p A := by
  have h (x : ℝ) : scorePl X p A x = scoreM Y p A x := by
    funext n
    simp only [scorePl, scoreM, Pi.add_apply, rentPl, rentM, Glyph.preamblePl,
      Glyph.preambleM, menus]
  funext k
  exact mark_birth (aquaPl X p A) (aquaM Y p A) (k := k + 1)
    (fun j _ x => congrFun (h x) j) k (Nat.lt_succ_self k)

theorem taylor {B : Deck G} (X : RichBook B) (Y : BookM B)
    (menus : ∀ d r u, X.menu d r u = Y.inkM d r u)
    {A : Booked B} (M : MS_Data G A) (T : Prescription B) :
    TaylorOKPl M X T ↔ TaylorOKM M Y T := by
  constructor
  · intro H
    exact ⟨H.bulk, fun d i => (horizon X Y menus T.team (T.fees d i)) ▸ H.mark d i⟩
  · intro H
    exact ⟨H.bulk, fun d i => (horizon X Y menus T.team (T.fees d i)).symm ▸ H.mark d i⟩

/-- All direct mixed-geometry rescalings and removals hold for the exact
prescription delivered by the moving correlation. -/
theorem profiles (R : Run G) (hG : G.Simple) {B : Deck G} (e : nativeDeck R = B)
    {A : Booked B} {M : MS_Data G A} {T : Prescription B}
    (h : MovingOn R e A M T) : MixedStory.AllProfiles M (warehouse R) T := by
  subst B
  obtain ⟨_, _, hm⟩ := h
  let V := warehouse R
  have ht := (hm.apply_M 0).draw.high
  change TaylorOKPl M (FVAAlt2.Shop.richBook (nativeDeck R) V.F V.H V.S V.h V.acts) T at ht
  have hM := (taylor _ (V.native (nativeDeck R)) (NativeFormalStencilAgreement.menu V _) M T).mp ht
  exact ⟨hM, fun _ _ _ p μ w l hp => MixedStory.clears M V p T μ w l hp hG hM⟩

theorem windows {R : Run G} (h : NativeFVAPlateau.Correlations R) :
    NativeFVAPlateau.Funded R.family.path.levels := by
  obtain ⟨Z, C, _⟩ := h
  exact ⟨Z, C.holds⟩

theorem common (R : Run G) (hG : G.Simple) (h : NativeFVAPlateau.Correlations R) :
    ∃ (B : Booked (wings G)) (M : MS_Data G (angular B (warehouse R)))
      (T : Prescription (wings G)), RadL.Reg B ∧
      MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B (warehouse R)) M T ∧
      MixedStory.AllProfiles M (warehouse R) T := by
  obtain ⟨B, M, T, _, _, hB, hm, _⟩ := shared R hG (windows h)
  exact ⟨B, M, T, hB, hm, profiles R hG _ hm⟩

end YM.Integration.NativeFormalMixedProfiles
end
