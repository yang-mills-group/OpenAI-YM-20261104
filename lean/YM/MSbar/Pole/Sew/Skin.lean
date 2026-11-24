import YM.MSbar.Pole.Sew.Ticket

/-!
# Kinematic capture, retaining all dummy-slot laws and orientations

Parents acquire dependence on all output momenta (except root) and angles in Y,
regardless of whether the actual reading uses them; children likewise controlled
through such full slot sets. This generality permits reused root choices.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Sew
open Function Filter Set Ambient Momentum Age Mellin place Symbol Tip
open scoped Topology ContDiff Classical BigOperators
variable {I : Type} [Fintype I] {n : ℕ}

namespace Thread
variable (T:Thread I)
def inputs := insert T.left (insert T.right T.output)
/-- output momentum slots, except chosen anchor, and all surviving vector slots. -/
def layout (L : Finset I) := (T.output.erase T.root) ∪ L

variable {T} {Y : Finset I}

/-- Incidence requirements on the cut-off graph and remaining angles. Doesn't
specify weights or perturbative slots. -/
structure Fits (T : Thread I) (U : Finset I) : Prop where
  root_mem : T.root ∈ T.output
  distinct : T.left ≠ T.right
  left_out : T.left ∉ T.output
  right_out : T.right ∉ T.output
  reserve : Disjoint T.chain.reads U
  fresh : Disjoint T.inputs (T.chain.reads ∪ U)
  chain : T.chain.usable

lemma Tight (h : Fits T Y) {K : ℂ→Cloud I} {s : ℂ} (hf:Shape (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) (K s)) (r:ℝ) :
    Signature (T.layout Y) Y (T.spun r K s) := by
  let C := (Chain.term T.left (dimension s) (K s) T.chain)
  have hv : Shape (insert T.left ((T.inputs ∪ (T.chain.reads∪ Y)) \ T.chain.reads)) ((T.chain.reads ∪ Y) \ T.chain.reads) C:= Chain.uses hf T.chain T.left (fun z=> Finset.disjoint_left.mp h.fresh (by simp [inputs]) z) _
  constructor
  · intro n i x y hx
    change _ * C _ (T.warp _ (i,x))= _ * C _ (T.warp _ (i,y)); congr 1; apply hv.sees; intro j hj; rw [T.warps,T.warps]; unfold fill; by_cases hl:j=T.left
    · subst j; rw [update_self,update_self]
    rw [update_of_ne hl,update_of_ne hl]; by_cases hr:j=T.right
    · subst j; rw [update_self,update_self]
    rw [update_of_ne hr,update_of_ne hr]; by_cases hZ:j=T.root
    · subst j; simp only [anchor,update_self]; congr 1
      exact Finset.sum_congr rfl fun l hh=> hx l (Finset.mem_union_left _ hh)
    unfold anchor; rw [update_of_ne hZ,update_of_ne hZ]; apply hx j
    simp only [inputs,Finset.mem_union,Finset.mem_insert,Finset.mem_sdiff] at hj
    simp only [layout,Finset.mem_union,Finset.mem_erase]
    tauto
  intro i hi n p x
  have ht:i∈ T.chain.reads ∪ Y:=Finset.mem_union_right _ hi
  have he:i∉T.inputs:=fun u=>Finset.disjoint_left.mp h.fresh u ht
  simp only [inputs,Finset.mem_insert,not_or] at he
  have hs(v): T.warp n (p,update x i v) = update (T.warp n (p,x)) i v := by
    rw [T.warps,T.warps]; exact independent _ _ _ _ x v he.2.2 (Ne.symm (ne_of_mem_of_not_mem h.root_mem he.2.2)) p he.1 he.2.1
  change Along (fun v=> _ * C n (T.warp n (p,update x i v))); simp_rw [hs]
  exact (hv.angle i (Finset.mem_sdiff.mpr ⟨ht,fun h₁=> Finset.disjoint_left.mp h.reserve h₁ hi⟩) ..).scale _

lemma joined (h: Fits T Y) {K : ℂ→Cloud I} {k:ℕ} (s:ℝ) (hs:0<s) (hk:Vortex k K) (hp:Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) K) : Skin k (T.spun s K) := T.collect hk _ hs hp h.chain (Finset.subset_union_left)
lemma fused (h : Fits T Y) {K : ℂ→Cloud I} {k:ℕ} (s:ℝ) (hs:0<s) (hk:Vortex k K) (hp:Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) K) (μ:ℝ) (hμ : 0<μ):
    Vortex k (Integrates μ (T.spun s K)) ∧ Acts (T.layout Y) Y (Integrates μ (T.spun s K)) := by
  have he:= joined h s hs hk hp; refine ⟨he.operate μ hμ,?_⟩
  unfold Acts
  filter_upwards [Skin.statuses he,hp] with z hv hh
  let Z:= T.spun s K z; let F(n): External I n→ℂ:= fun x=> omega n Z x (dimension z)
  rw [show Integrates μ (T.spun s K) z=factor μ z • F from funext fun n=>funext fun x=>mul_comm ..]
  exact (loved hv.1 hv.2 (Tight h hh s) (dimension z)).scale _

/-- Adding edge graphs with their ordinary signs, before applying the scale operation. -/
lemma crossing {F G:Cloud I} {J K B C: Finset I} (hu:Shape J B F) (hv:Shape K C G) (ha:Disjoint B K) (hb:Disjoint C J) : Shape (J∪K) (B∪C) (F*G):= by
  refine ⟨fun n x y hx=>congr_arg₂ (·*·) (hu.sees n x y fun i hi=>hx i (Finset.mem_union_left _ hi)) (hv.sees n x y fun i hi=>hx i (Finset.mem_union_right _ hi)),?_⟩
  intro i hi n x; rcases Finset.mem_union.mp hi with h|h
  · have hp t : (F*G) n (update x i t) = G n x* F n (update x i t) := by
        rw [Pi.mul_apply,Pi.mul_apply,hv.sees n (update x i t) x (fun j hj=> update_of_ne (ne_of_mem_of_not_mem hj (fun z=>Finset.disjoint_left.mp ha h z)) _ _),mul_comm]
    simp_rw [hp]; exact (hu.angle i h ..).scale _
  have hp t : (F*G) n (update x i t) = F n x * G n (update x i t) := by rw [Pi.mul_apply,Pi.mul_apply,hu.sees n (update x i t) x (fun j hj=>update_of_ne (ne_of_mem_of_not_mem hj (fun z=>Finset.disjoint_left.mp hb h z)) _ _)]
  simp_rw [hp]; exact (hv.angle i h ..).scale _
end Thread
end YM.MSbar.Pole.Sew
