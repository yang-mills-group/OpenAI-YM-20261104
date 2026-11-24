import YM.MSbar.Pole.Symbol.Heat
/-! Assign momenta at one sewing. Deltas stripped, root argument always computed.
Allows charts with open source bits and dummy slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Sew
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n : ℕ}
namespace Tip
variable (U : Finset I) (z a b : I)
def anchor (x:External I n): External I n:= update x z (-∑ i∈U.erase z,x i)
def fill (x : External I n) (v : place n): External I n:= update (update (anchor U z x) b (-v)) a v
def patch (S : I) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E](X:E→L[ℝ]External I n)(Y:E→L[ℝ]place n): E→L[ℝ]External I n:= ContinuousLinearMap.pi fun i=> if i=S then Y else (ContinuousLinearMap.proj i).comp X
lemma patched {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (X:E→L[ℝ]External I n)(Y:E→L[ℝ]place n) (x:E): patch z X Y x= update (X x) z (Y x) := by funext i; by_cases he:i=z; subst i; simp [patch]; simp [patch,he]

def gather (n:ℕ): External I n →L[ℝ] place n:= ∑ i∈U,ContinuousLinearMap.proj i
@[simp] lemma gathered (x:External I n):gather U n x=∑ i∈U,x i:=by unfold gather; simp

def bead (n:ℕ): External I n →L[ℝ] External I n:= patch z (ContinuousLinearMap.id ..) (-gather (U.erase z) n)
lemma beads (x:External I n): bead U z n x=anchor U z x:=by rw [bead,patched,anchor]; simp

def bar (n:ℕ): place n × External I n →L[ℝ] External I n :=
  let Y := ContinuousLinearMap.snd ℝ (place n) _; let X := ContinuousLinearMap.fst ℝ _ (External I n)
  patch a (patch b ((bead U z n).comp Y) (-X)) X
lemma barred (x:External I n) (v:place n):bar U z a b n (v,x)=fill U z a b x v:=by
  unfold bar fill; simp only [patched]; rw [ContinuousLinearMap.comp_apply,beads]; rfl

private lemma attends (V:Finset I) (x:External I n) (p:I) (d:place n) (he:p∉V): ∑ i∈V,(update x p d) i= ∑ i∈V,x i := by
  apply Finset.sum_congr rfl; exact fun i hi=> update_of_ne (ne_of_mem_of_not_mem hi he) _ _

-- update through when support is outside whole routing
lemma independent (x:External I n) (v : place n) {j:I}(he:j∉U) (hu:j≠z) (q:place n) (h₁:j≠a)(h₂:j≠b):
    fill U z a b (update x j v) q= update (fill U z a b x q) j v:=by unfold fill anchor; rw [attends _ x j v (by simp [he]),update_comm hu,update_comm h₂,update_comm h₁]
private lemma promote {E A:Type} (f:E→A) (p:I)(x:I→E)(v:E):update (f∘x) p (f v)= f ∘ update x p v:=by
  ext1 i; by_cases he:i=p; subst i; simp; simp [he]
lemma turns (J:place n≃ₗᵢ[ℝ]place n)(x:External I n)(v:place n): fill U z a b (J∘x) (J v)= J ∘ fill U z a b x v :=by
  unfold fill anchor; simp only [comp_apply (f:= (J:place n→place n))]; rw [← map_sum,← map_neg,← map_neg,promote,promote,promote]
lemma pads (x:External I n) (v:place n): fill U z a b (pad n∘x) (pad n v)=pad n ∘ fill U z a b x v :=by
  unfold fill anchor; simp only [comp_apply (f:= (pad n:place n→place (n+1)))]; rw [← map_sum,← map_neg,← map_neg,promote,promote,promote]
private lemma grows (V : Finset I) (k:I) (p:k∈V)(v:place n)(x:External I n)(r:ℝ):
    update (move V r x) k (r • v)=move V r (update x k v):=by funext i; by_cases hi:i=k; subst i; simp [move,p]; simp [move,hi]
lemma enlarges (V : Finset I) (p:U ⊆ V) (hz:z∈U) (ha:a∈V)(hb:b∈V)(x:External I n)(v:place n)(r:ℝ): fill U z a b (move V r x) (r • v)=move V r (fill U z a b x v):=by
  unfold fill anchor
  rw [show ∑ i∈U.erase z,move V r x i = r • (∑ i∈U.erase z,x i) from ?_, ← smul_neg,← smul_neg,grows _ z (p hz),grows _ b hb,grows _ a ha]
  rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i hi=>if_pos (p (Finset.mem_of_mem_erase hi))

/-- Bridge left p from legs left except first incidence `a`. -/
def solve (L:Finset I)(n:ℕ): External I n→L[ℝ]place n:= -(gather L n).comp (bead U z n)
lemma inferred (L:Finset I)(x:External I n): solve U z L n x= -∑ i∈L,anchor U z x i:=by simp only [solve, ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,beads,gathered]
end Tip
end YM.MSbar.Pole.Sew
