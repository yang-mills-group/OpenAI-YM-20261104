import YM.MSbar.Pole.Sew.Skin
/-! Bridge momentum preserving orientation, tensor laws and shape, even when
paired roots of source terms have dependent momenta. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Sew.Thread
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Tip
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n : ℕ} (T:Thread I)(L : Finset I)

def momentum := solve T.output T.root L

def load (F : Screened I) : Cloud I:=fun n x=> F n (momentum T L n x,x)
def twig (s:ℝ) (G:ℂ→Cloud I) : ℂ→Cloud I:= fun z=>T.load L (T.spun s G z)

private theorem commutes {m:ℕ} (P:place n →L[ℝ] place m) (x:External I n):
    T.momentum L m (P∘x)= P (T.momentum L n x):=by
  unfold momentum; rw [inferred,inferred,map_neg,map_sum]; congr 1; apply Finset.sum_congr rfl
  intro i hi; unfold anchor; by_cases he:i=T.root
  · subst i; rw [update_self,update_self,map_neg,map_sum]; rfl
  simp [he]

lemma transport {W:Screened I} (h:Texture W): Tensor (T.load L W):=by
  constructor
  · intro n J x; unfold load; rw [show T.momentum L n (J∘x)=_ from commutes T L J.toLinearIsometry.toContinuousLinearMap x]; exact h.moves n J _ _
  intro n x; unfold load; rw [commutes,h.agrees]
lemma rated {R:ℝ} {W:ℂ→Screened I} (h:Sweep (zone R) W): Meridian (zone R) (fun z=> T.load L (W z)) := by
  refine ⟨fun n=>?_,fun z hz=> T.transport L (h.texture z hz)⟩
  let A:= (T.momentum L n).prod (ContinuousLinearMap.id ℝ _)
  exact (h.budget n).pull A (r:=ticket _) Bills.self (Bills.const _)
lemma paid {K:ℂ→Screened I} {k} (h:Skin k K): Vortex k (fun z=> T.load L (K z)):= by
  obtain ⟨R,G,hr,H,h⟩:=h; exact ⟨R,_,hr,rated T L H,fun _ hz n x=>h _ hz n _⟩

variable {T L}
lemma moment_agree (hl:L ⊆ T.output) {Y:Finset I} (x y : External I n) (h : ∀ i∈T.layout Y,x i=y i) : momentum T L n x=momentum T L n y:=by
  unfold momentum; rw [inferred,inferred]; congr 1; apply Finset.sum_congr rfl; intro i hi
  unfold anchor; by_cases he:i=T.root
  · rw [he,update_self,update_self]; congr 1; exact Finset.sum_congr rfl (fun i hi=>h i (Finset.mem_union_left _ hi))
  rw [update_of_ne he,update_of_ne he]; exact h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hl hi⟩))
lemma unscathed (hl:L⊆T.output) {i:I} (h:i∉T.output)(x:External I n)(w): T.momentum L n (update x i w)=T.momentum L n x:= by
  refine moment_agree (T:=T) (Y:=∅) hl _ _ (fun j hj=>update_of_ne ?_ _ _)
  apply ne_of_mem_of_not_mem _ h; simp [layout] at hj; exact hj.2
lemma tokens {H: Screened I} {Y: Finset I} (hl:L ⊆ T.output) (he:Disjoint T.output Y) (p:Signature (T.layout Y) Y H):
    Shape (T.layout Y) Y (T.load L H):= by
  constructor
  · intro n x y hh; unfold load; rw [moment_agree hl x y hh]; exact p.listens  n _ _ _ hh -- dots?
  intro i hi n x; unfold load; simp_rw [unscathed hl (fun z=>Finset.disjoint_left.mp he z hi)]
  exact p.tone i hi ..
lemma offered {Y:Finset I} (h:Fits T Y) {K : ℂ→Cloud I} {k:ℕ} (s:ℝ) (hs:0<s) (hk:Vortex k K) (hp:Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) K) (hl:L ⊆ T.output) :
    Vortex k (T.twig L s K) ∧ Acts (T.layout Y) Y (T.twig L s K):= by
  refine ⟨paid T L (joined h s hs hk hp),Filter.Eventually.mono (p:=fun x=>Shape _ _ (K x)) hp (fun z hz=>?_)⟩
  exact tokens hl (Finset.disjoint_left.mpr fun i hi hg=> Finset.disjoint_left.mp h.fresh (by simp [inputs,hi]) (Finset.mem_union_right _ hg)) (Tight h hz _)
end YM.MSbar.Pole.Sew.Thread
