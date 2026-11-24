import YM.SchemeConversionRG11.Field.Affine
import YM.SchemeConversionRG11.Foundation.JetAlgebra

/-! Jet versions; one filtration through all finite horizons. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11
namespace Orbit

open Filter Function Affine Series Pert.Position Horizon
open scoped Topology ContDiff

variable {G : Gauge} {F : Labels.Frames G} {d e : ℕ} {p : ℕ}

section step

local notation "U" => Buffer F d
variable {B C : Series (Buffer F d)} {x : Series ℝ}

def chain (B C : Series (Buffer F d)) := liftJet (fun u : U × U ↦ after u.1 u.2) (both B C)

theorem chain_jet {a b : ℝ → U} (h : Represents p a B) (k : Represents p b C) :
    Represents p (fun t ↦ after (a t) (b t)) (chain B C) :=
  (h.pair k).lift after_regular.contDiffAt

theorem undo_jet {a : ℝ → U} (h : Represents p a B) (hm : Fits (B 0)) :
    Represents p (undo ∘ a) (liftJet undo B) := h.lift (undo_smooth hm)

theorem revert_left (h : Fits (B 0)) : chain B (liftJet undo B) = 0 := by
  funext i
  have H := trunc_represents B i
  have hd := chain_jet H (undo_jet H h)
  have he := H.regular.continuousAt.tendsto
  rw [H.value] at he
  exact (hd.germ (he.eventually h.surround |>.mono fun t ht ↦ (after_undo ht).symm)).unique
    (Represents_zero i) i le_rfl

theorem revert_right (h : Fits (B 0)) : chain (liftJet undo B) B = 0 := by
  funext i
  have H := trunc_represents B i
  have hd := chain_jet (undo_jet H h) H
  have he := H.regular.continuousAt.tendsto
  rw [H.value] at he
  exact (hd.germ (he.eventually h.surround |>.mono fun t ht ↦ (undo_after ht).symm)).unique
    (Represents_zero i) i le_rfl

theorem reindex (h : x 0 = 0) : subJet (chain B C) x = chain (subJet B x) (subJet C x) := by
  unfold chain; rw [both_subst h, ← liftJet_subst after_regular.contDiffAt h]

theorem through (A B C D : Series U) (h : Through p A B) (k : Through p C D) :
    Through p (chain A C) (chain B D) := (h.both k).lift after_regular.contDiffAt

theorem starting (B C : Series U) : chain B C 0 = after (B 0) (C 0) := by
  unfold chain; rw [liftJet_zero]; rfl
end step

/-- A formal move at each horizon. -/
abbrev Schedule (F : Labels.Frames G) := (i : ℕ) → Series (Buffer F i)
def Guided (n : ℕ) (V : Schedule F) (h : ℕ) :=
  ∀ ⦃d e⦄, ∀ he : d ≤ e, e ≤ h → Through n (fun j ↦ restr F he (V e j)) (V d)

theorem synchronise {s t : Schedule F} {h : ℕ}
    (hs : Guided p s h) (ht : Guided p t h) : Guided p (fun d ↦ chain (s d) (t d)) h := by
  intro d e he hl
  have H := trunc_represents (s e) p
  have K := trunc_represents (t e) p
  have hp := (H.linear (F := Buffer F d) (restr F he)).congr (hs he hl)
  have hq := (K.linear (F := Buffer F d) (restr F he)).congr (ht he hl)
  have hr := (chain_jet H K).linear (F := Buffer F d) (restr F he)
  apply hr.unique
  exact (chain_jet hp hq).germ (Eventually.of_forall fun _ ↦ nested he _ _)

theorem reverse_guides {s : Schedule F} {h : ℕ} (hs : Guided p s h) (hx : ∀ d ≤ h, Fits (s d 0)) :
    Guided p (fun d ↦ liftJet undo (s d)) h := by
  intro d e he hl
  have H := trunc_represents (s e) p
  have hk := hx e hl
  have hh := (undo_jet H hk).linear (F := Buffer F d) (restr F he)
  have hu := H.regular.continuousAt.tendsto
  rw [H.value] at hu
  have hw : ∀ᶠ t in 𝓝 (0:ℝ), Fits (trunc (s e) p t) := hu.eventually (Fits.surround hk)
  have hf := ((H.linear (F := Buffer F d) (restr F he)).congr (hs he hl))
  have hz := undo_jet hf (hx d (he.trans hl))
  have eq' : ⇑(restr F he) ∘ (undo ∘ trunc (s e) p) =ᶠ[𝓝 (0:ℝ)] undo ∘ (⇑(restr F he) ∘ trunc (s e) p) := by
    filter_upwards [hw] with t ht
    simp only [Function.comp_apply]
    exact undo_restr he ht
  exact hh.unique (hz.germ eq')

theorem coupling_guides {s : Schedule F} {h : ℕ} {g : Series ℝ} (hg : g 0 = 0)
    (hs : Guided p s h) : Guided p (fun d ↦ subJet (s d) g) h := by
  intro d e he hl
  have H := trunc_represents (s e) p
  have hk := (trunc_represents g p)
  exact ((H.subJet hk hg).linear (F := Buffer F d) (restr F he)).unique
    (((H.linear (F := Buffer F d) (restr F he)).congr (hs he hl)).subJet hk hg)

/-- Finite evaluating representative (maybe taking a *fixed larger* internal order).
    Compatible on fields exactly, for every t (no assertion they are all legal frames there). -/
theorem trunc_restrict {s : Schedule F} {h : ℕ} (hm : Guided p s h) (w : d ≤ e) (hw : e ≤ h) (t : ℝ) :
    restr F w (trunc (s e) p t) = trunc (s d) p t := by
  unfold trunc curve; simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl; intro i hi
  exact congrArg (fun v : Buffer F d ↦ (t^i • v : Buffer F d)) (hm w hw i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
end Orbit
end YM.SchemeConversionRG11
