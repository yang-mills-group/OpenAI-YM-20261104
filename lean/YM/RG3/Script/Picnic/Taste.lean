import YM.RG3.Script.Marker
import YM.RG3.Held.Typed

/-! # The whole powered Scripts purchase UNIFORMLY on announced held
arguments or test derivatives (choose any test population cap). Re-use the
seat receipts around Test; HERE permit incorporated new captions and rates
from f, not requiring preservation of old caption seats/values. This version
does not infer multilinearity in X from pricing or differentiating in Ω BEHIND
switches: Ω parameters are supplied passively and books on both d and drafts
must be compiled independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {V : Type*}[DecidableEq V]{R:Census V}{n : Side}{G : Gauge}{P : Rep G n}
  (X : Type*) (ζ:V→Site n)

/-- Exact testing layout at all parameters. Member abstraction (not assuming
funds after embedding). Include rank-zero caption supports common on tests.
-/
structure Taste (P : Rep G n) (R:Census V) where
  menu : View X V G n P R
  root : menu.origins=ζ
  tag : ℕ→R.Mode
  site : ℕ→Support n
  score : X→ℕ→ℂ

namespace Taste
variable {X ζ}(T : Taste X ζ P R)
def leaf (x : X): Deck R P:= ⟨T.menu.terms x,⟨T.tag,T.site,T.score x⟩⟩
structure Snacks (w : V→ℝ)(u c γ b a:ℝ) where
  strong : T.menu.Passport w u c γ b
  active : ∀ x,(T.leaf x).captions.Sound ζ
  gold : ℕ → ℝ
  given i : 0 ≤ gold i ∧ ∀ x,‖T.score x i‖ ≤ gold i
  ticket v : SumBudget (per P.p.B P.p.supportExponent w T.tag T.site gold v) a

lemma snack {w u c γ b a}(h:T.Snacks w u c γ b a) (x): (T.leaf x).Active ∧ (T.leaf x).Budget w u c γ b a := by
  obtain ⟨H,B⟩:=T.menu.identifies h.strong x
  have ht: ζ=(T.leaf x).contents.origins:=T.root.symm
  refine ⟨⟨H,ht ▸ h.active x⟩, B,⟨fun i=>budget_mono (h.ticket i) (per_nn (fun i=> (B.pure i).le) (f:=fun i=>‖T.score x i‖) (fun _=>norm_nonneg _) · _ ) (fun y=> ?_)⟩⟩
  change (per _ _ w T.tag T.site (fun i=> ‖T.score x i‖) i y) ≤ _; unfold per expense; split_ifs
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((h.given _).2 _) (Real.exp_pos _).le) (Poly.worth B.pure _).le
  rfl

/-- Log prices only, for the target Draft. -/
structure Store (w: V→ℝ) (u c a:ℝ) where
  fit x : Article.Contents (T.menu.terms x)
  here i : 0 < w i
  globe x i : w i*‖T.menu.global x i‖≤u
  white : ℕ→ℝ
  present i : 0≤white i ∧ ∀ x s,s∈ (T.menu.rays i).val → P.p.supBounds (ζ s) (T.menu.branch i) (T.menu.regular x i) (white i)
  warrant i : SumBudget (T.menu.costR w white i) c
  sound x : (T.leaf x).captions.Sound ζ
  gold : ℕ→ℝ
  given i : 0 ≤ gold i ∧ ∀ x, ‖T.score x i‖ ≤ gold i
  ticket v : SumBudget (per P.p.B P.p.supportExponent w T.tag T.site gold v) a

def gather {w u c γ b a}(h:T.Snacks w u c γ b a): T.Store w u c a:= ⟨fun i=>⟨(h.strong.active i).proper,(h.strong.active i).pins,(h.strong.active i).regular⟩,h.strong.radii,h.strong.unit,h.strong.white,
    fun i=>⟨(h.strong.bulk i).1,fun x q hp=>(congrFun T.root q) ▸ (h.strong.bulk i).2 x q hp⟩,h.strong.bulkCap,h.active,h.gold,h.given,h.ticket⟩
lemma shelf {w u c a}(h:T.Store w u c a)(x:X): Article.LogBounds (T.menu.terms x) w u c ∧ (T.leaf x).captions.Paid w P.p a:= by
  refine ⟨⟨h.globe x,h.white,fun i=>?_,h.warrant⟩,⟨fun i=>?_⟩⟩
  · change 0≤h.white i ∧ ∀ s∈ (T.menu.rays i).val,P.p.supBounds (T.menu.origins s) _ _ _; rw [T.root];exact ⟨(h.present i).1,(h.present i).2 x⟩
  apply budget_mono (h.ticket i) (per_nn (fun i=> (h.here i).le) (f:=fun i=>‖T.score x i‖) (fun _=>norm_nonneg _) · _)
  intro y
  change per _ _ w T.tag T.site _ i y ≤ _; unfold per expense; split_ifs
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((h.given y).2 x) (Real.exp_pos _).le) (Poly.worth h.here _).le
  rfl

structure Menu (w:V→ℝ) (vac mark:ℝ) where
  store : ∀ x,Billboard (T.menu.terms x) w P.p.B (P.p.supportExponent+1) vac mark
  vac_fixed x y : (store x).vac=(store y).vac
  bill_fixed x y : (store x).bill=(store y).bill
end Taste
end YM.RG3.Script.Picnic
