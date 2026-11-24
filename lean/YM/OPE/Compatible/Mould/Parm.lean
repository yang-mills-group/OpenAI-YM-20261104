import YM.OPE.Compatible.Mould.Kick
/-!
# Radar induction tool
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d k i j m s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w' wV:V→ℝ}{r t:ℕ→ℝ}{Y:V→Mints E→L[ℝ] Mints E}
namespace Aeon
variable (U:Aeon V T X w')(Δ:Submodule ℝ (Fruition X (μ k))) (R:V→Submodule ℝ (Mints E))
local notation "F!"=> Fruition X (μ k)
lemma Decks (he:k<d)(hz:0≤wV)(P:F!→ Prop)(S:Mints E→Prop)
 (hS:S 0)(hp:∀ x y,S x→S y→ S (x+y))(hV:∀ i,
 ∀ x:U.flag k i,x.val∈ R i→ U.read k he i x∈Δ)(ht:∀ p:F!,∀ (i:V)(q:U.flag k i),P p→ S q.val→ P (p-U.read k he i q))
 (C:∀ (p:V→F!), Wealth (fun i=>(p i).val) w' wV→ (∀ i,p i ∈ Δ)→ (∀ i,P (p i))→∀ j:Fin s,(∀ i,trims j.val (p i).val)→∃ f:∀ j,U.flag k j, Wealth (fun j=>(f j).val) w' wV∧ (∀ j,(f j).val∈ R j) ∧∀ i,trims j.val (f i).val ∧ S ((f i).val)∧ trims (j.val+1) (p i-U.read k he i (f i)).val)
 (p:V→ F!)(hy:Wealth (fun i=>(p i).val) w' wV)(hs:∀ i,p i∈ Δ)(hq:∀ i,P (p i))(j:ℕ)(hj:j≤s)(hn:∀ i,trims j (p i).val): ∃ f:∀ j,U.flag k j, Wealth (fun i=>(f i).val) w' wV∧∀ i,(f i).val∈ R i∧ U.read k he i (f i)=p i∧ trims j (f i).val∧ S (f i).val:=by
     induction hj using Nat.decreasingInduction generalizing p with
     | self=> exact ⟨0,wealthZ .., fun i=>⟨(R i).zero_mem,(map_zero _).trans (Subtype.ext (hn i).limb.symm),fun i _=>rfl,hS⟩⟩
     | of_succ j hj IH=>
         let i:Fin s:=⟨j,hj⟩; obtain ⟨f,h,hF,hX⟩:= C p hy hs hq i hn; let x(w:V):= U.read k he w (f w); let z:=p-x; obtain ⟨y,hY,hP⟩:=IH z (subW U.non hz hy (U.bulk he f h)) (fun i=>Submodule.sub_mem Δ (hs i) (hV i _ (hF i))) (fun i=> ht (p i) i (f i) (hq i) ((hX i).2.1)) fun i=> (hX i).2.2; refine ⟨y+f, anthW U.non hz hY h, fun i=>⟨(R i).add_mem (hP i).1 (hF i),?_, ((hP i).2.2.1.drop (Nat.le_succ j)).plus (hX i).1,hp _ _ (hP i).2.2.2 (hX i).2.1⟩⟩; rw [Pi.add_apply,map_add,(hP i).2.1]; exact sub_add_cancel ..
end Aeon
end YM.OPE.Hark
