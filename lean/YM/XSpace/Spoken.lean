import YM.XSpace.Rain

/-! # Extensional reach of color-pair tests

With tests of arbitrary arities get *every* inside direction of the finite
used-position jet space of legs, incl at exact derivative degrees. `Flavor` = full dual of
real on-shell leg. Using the existing Maxwell `ranging` theorem, on the REAL
covariance, so in this part we don't use null-leading data of unshared interior legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter MvPolynomial Maxwell Maxwell.Free Next.Rank.Normal
open scoped BigOperators Topology Classical

abbrev Supply (S : Finset E4) (h : ℕ) := ((S:Set E4)) → (j:Fin (h+1))→ Flavor j
variable {G : Gauge} (C₀:G.ColorIndex) {x y : E4} (h : ℕ)
variable {S L : Finset E4} {A:Finset (World G)}
def task (x : (S:Set E4)) (j : Fin (h+1)) (p:Flavor j): Supply S h:=Pi.single (M:=fun _=> (i:Fin (h+1))→ Flavor i) x (Pi.single (M:=fun i:Fin (h+1)=> Flavor i) j p)
def Good (S : Finset E4) (h : ℕ) (A : Finset (World G)) := ∀ i∈A,i.1∈S ∧ i.2.1.1≤h

def pronounce (S:Finset E4) (h:ℕ) (i : World G): Supply S h:= if hi:i.1∈S∧i.2.1.1≤h then task h ⟨i.1, hi.1⟩ ⟨i.2.1.1,by exact Nat.lt_succ_of_le hi.2⟩ i.2.1.2 else 0

def voice (S : Finset E4) (h:ℕ) (C₀ : G.ColorIndex) (v:Ph): Module.Dual ℝ (Supply S h):= if hi:v.1∈S then 0 else
  ∑ x:(S:Set E4),∑ j:Fin (h+1), (assay C₀ (sub_ne_zero.mpr (show x.val≠v.1 from fun e=> hi (e ▸ (show x.val∈S from x.property)))) j 0).flip v.2 ∘ₗ (LinearMap.proj (R:=ℝ) j) ∘ₗ (LinearMap.proj (R:=ℝ) x)
lemma chorus (v : Ph) (he : v.1∉ S) (Z : Supply S h): voice S h C₀ v Z=∑ x:(S:Set E4), ∑ j:Fin (h+1), fare C₀ (Z x j) v.2 (x.val-v.1):=by rw [voice,dif_neg he,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [LinearMap.sum_apply]; rfl
lemma chord (v : Ph) (he : v.1∉ S) (x : (S:Set E4)) (j : Fin (h+1)) (p:Flavor j) : voice S h C₀ v (task h x j p)= fare C₀ p v.2 (x.val-v.1):=by
  have hz (i:(S:Set E4)) (k : ℕ): fare C₀ (0:Flavor k) v.2 (i.val-v.1)=0:= map_zero ((assay C₀ (sub_ne_zero.mpr (show i.val≠v.1 from fun h=> he (h ▸ (show i.val∈S from i.property)))) _ _).flip v.2)
  rw [chorus _ _ v he, Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (fun i _ hi=> by simp [task,hi,hz])]; simp only [task,Pi.single_eq_same]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun i _ hi=> by rw [Pi.single_eq_of_ne hi,hz]), Pi.single_eq_same]

def backed {S:Finset E4} {h:ℕ} (F:Module.Dual ℝ (Supply S h)) : Lane G:= fun e z=> if z.2.2=e then (F (pronounce S h z):ℂ) else 0
lemma bow (x : Ph) (i : World G) (a : G.ColorIndex) (hf : x.1∉ S) (hi : i.1∈S ∧ i.2.1.1≤h):
    fast S x a i=backed (voice S h C₀ x) a i :=by
  let y : Ph:= x; rw [backed,pronounce,dif_pos hi]; unfold fast cellL lit dot; rw [(Cold S G).symm,cold_in hi.1,show (Kf G).cov i _= _ from colors C₀ (show i.1≠x.1 from fun e=> hf (e ▸ hi.1)) i.2.1 ⟨0,x.2⟩ i.2.2 a, chord C₀ h x hf]

end YM.XSpace.Legs
