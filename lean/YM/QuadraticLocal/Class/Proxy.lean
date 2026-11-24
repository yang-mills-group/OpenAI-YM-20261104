import YM.QuadraticLocal.Germ.Focal
import YM.QuadraticLocal.Germ.Shell
/-!
# Displaying each pupil's Gallery on native local-comparison budgets & addresses

Continue even in REAL held-slot convention. When a source is given already complex, these
estimates apply too (on restricting scalars, charges on the same entire spaces and including
all TestSpace independent stencils). They don't assert that after the analytic comparison each
individual real-linear density-log *term* was a complex-linear one. See `Smalt` at unmarked-side
and rough-analytic estimates for complex projections; full complex-linear reclosure for these
presentations isn't conducted here. All prices below are in the same strong ℂ norms on terms
and for independent tests, whether they are real linear or complex linear.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QuadraticLocal.Display
open Function Filter Finset Lattice Wilson RG Ac Marker Overlay RG3 RG3.Held RG3.Forms Press
open Push.Corrected Push.AbsoluteSums MeasureTheory Extra.Trajectories Next.Foundations Push.Local
open RG3.Script.Picnic Integration.LocalComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V][Nonempty V]{R:Census V}{G:Gauge}{n:Side} {T:Type*}[Nonempty T]
variable {ι:Type*}[Countable ι]{P:Rep G n}{o:V→Site n} {w:V→ℝ}{q b c κ:ℝ}
local notation "Q"=> pin (α:=ι)
variable (A:Gallery T ι o P R)
open Affinity

namespace Proxy
variable {Y:V→Type}[∀ i,AddCommGroup (Y i)]{𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ][∀ i,Module 𝕜 (Y i)]
variable {α:Type}[Countable α]
variable (A':∀ i,Set (Y i))(K:∀ i,Submodule 𝕜 (Y i))

local notation "W"=>Wallet A'

structure Read (Y:Taste (Wallet A') o P R) :Prop where
  regular i U : Attn K A' ( Y.menu.rays i ).val (fun x => Y.menu.regular x i U)
  forced i j U : Attn K A' ( Y.menu.marks i j ).val (fun x => Y.menu.force x i j U)
  unit v : Attn K A' {v} (fun x => Y.menu.global x v)
  captions i : Attn K A' (Y.tag i).val (fun x => Y.score x i)

variable {A'} (M:Gallery (Wallet A') α o P R)(X:V→Support n)
variable (h:Collared X A' K P M) [Nonempty (Wallet A')]
local notation "D₁"=>  Display.taste M
-- declare only rows with matching i, nonempty labels, all stencils. Needed even for garbage empty values; cap.
local notation "f"=> pin (α:=α)
local notation "F₀"=> Article.Key ℕ R
local notation "n₀"=> pin (α:=F₀)
def stands : Set (ℕ×ℕ):= { s| ∃ j:Article.Key ℕ R, n₀ j=s.snd ∧ j.fst=s.fst ∧ (∀ v∈ ((D₁).menu.marks s.fst s.snd).val, X v⊆ (P.activities.forced s.fst).support)}
private lemma flow i j (t:W) : (D₁).menu.force t i j= ((article M t).impression ((view M).terms t) id).entries i j:=rfl
private lemma marks (i j:ℕ)(t:W): (D₁).menu.marks i j= ((article M t).impression ((view M).terms t) id).marks i j:=rfl
include h
lemma retention (he:∀ v,o v∈ X v): RetainsDeclared (stands M X) D₁ X:= by
    refine ⟨he,?_, ?_, ?_,?_⟩
    · intro i v hw; change v∈ (unpin _ (R.fire _) i).val at hw; change X v⊆ unpin (Display.focus M) univ i;
      by_cases he:i∈ Set.range f; obtain ⟨j,rfl⟩:=he; rw [unpin_pin] at hw ⊢; exact h.lamps.house j v hw
      rw [unpin_blank _ _ he]; exact subset_univ _
    · rintro i j ⟨u,hv,he,hH⟩ v hv; exact hH _ hv
    · intro i j hv t; rw [flow M i j t]; by_cases hp:j∈ Set.range n₀; swap; · rw [Article.scored_blank _ _ _ _ _ hp]
      obtain ⟨u,rfl⟩:=hp; rw [Article.scored_pin]; funext U; unfold Article.scored; split; swap; · rfl
      next hu=>
        change (M.K.hard t _ U).part u.snd.val=_; by_contra hn; apply hv; refine ⟨u,rfl,hu,?_⟩; rw [marks M _ _ t, Article.marked_pin,← show u.fst=i from hu]; exact ((h.hard.lesson _ _).each _).announces _ hn
    intro i v hv; change v∈ (unpin _ (R.fire _) i).val at hv; change X v⊆ unpin (Display.focus M) univ i; by_cases he:i∈ Set.range f
    · obtain ⟨j,rfl⟩:=he; rw [unpin_pin] at hv ⊢; exact h.lamps.house _ _ hv
    rw [unpin_blank _ _ he]; exact subset_univ _

lemma print : Read A' K D₁:=by
    let k:= K; let t:W:= Classical.arbitrary W; constructor
    · intro i U; change Attn K A' (unpin _ (R.fire _) i).val (fun t=> unpin (Display.drawn M t) _ i U); by_cases he:i∈ Set.range f
      · obtain ⟨j,rfl⟩:=he; rw [unpin_pin]; simp_rw [unpin_pin]; unfold Display.drawn; split; exact Attn.silent; exact h.lamps.adv j U
      simp_rw [unpin_blank _ _ he]; exact Attn.silent
    · intro i j U; simp_rw [flow M i j,marks M _ _ t]; by_cases he:j∈ Set.range n₀; obtain ⟨u,rfl⟩:=he; simp_rw [Article.scored_pin,Article.marked_pin]; unfold Article.scored; split; exact ((h.hard.lesson _ _).each _).advice; exact Attn.silent
      simp_rw [fun t:W=> Article.scored_blank (article M t) ((view M).terms t) id i j he]; exact Attn.silent
    · exact fun i=> Attn.silent
    intro i; change Attn K A' (unpin _ (R.fire _) i).val (fun t=> unpin (Display.nomad M t) _ i); by_cases he:i∈ Set.range f
    · obtain ⟨j,rfl⟩:=he; simp_rw [unpin_pin]; unfold Display.nomad; split; exact h.lamps.adv ..; exact Attn.silent
    simp_rw [unpin_blank _ _ he]; exact Attn.silent

end Proxy
end YM.QuadraticLocal.Display
