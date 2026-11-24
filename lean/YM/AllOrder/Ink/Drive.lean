import YM.AllOrder.Ink.Aisle
import YM.AllOrder.Ker.Matrix
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
section stalk
open Ker.Spine
abbrev BoardL (n:Side)(α β:Type):= Matrix (Leaf n α) (Leaf n β) ℝ
def sole : Shift (Arm 1)≃ Cover where
 toFun w:= point w 0
 invFun v:= fun i=> v i.2
 left_inv w:= funext (fun ⟨i,j⟩=> by fin_cases i; rfl)
 right_inv _:= rfl
lemma sole_size (w:Shift (Arm 1)): Laurent.size w=size (sole w):= by unfold size; rw [Fintype.sum_prod_type,Fin.sum_univ_one]; rfl
abbrev Stalk (α β:Type):= α→β→Cover→ℝ
def stick (F:Fan α β 1) : Stalk α β:= fun i j w=> F i ![j] (sole.symm w)
def Belt (F:Stalk α β) (a C:ℝ) := ∀ i j, Laurent.Width a C (F i j)
omit [Fintype α] [Fintype β]
lemma Belt.debt {F:Stalk α β}(h:Belt F a C) (he:b ≤ a)(h':C ≤ D): Belt F b D:= fun i j=>(h i j).mono he h'
lemma stick_belt {F:Fan α β 1} (h:Cap F a C): Belt (stick F) a C:= by
  intro i j; have ht:=budget_pull sole.symm sole.symm.injective (h i (![j])); simpa only [stick,Width,SumBudget,sole_size,Equiv.apply_symm_apply] using ht -- issue size used orientation simp infinite? size L

def direct (F:Stalk α β)(n:Side) : BoardL n α β:= Matrix.of fun i j=> ∑' w, if j.1=i.1+wrap n w then F i.2 j.2 w else 0
lemma direct_apply (F:Stalk α β)(i:Leaf n α)(j:Leaf n β): direct F n i j= ∑' w,if j.1=i.1+wrap n w then F i.2 j.2 w else 0:=rfl

variable {F:Stalk α β} (G:Belt F a C)(ha:0≤a)
include G ha
lemma regional (i:Leaf n α) (j:Leaf n β) : HasSum (fun w=>if j.1=i.1+wrap n w then F i.2 j.2 w else 0) (direct F n i j):= by
  let H:= (G i.2 j.2).summable ha; exact (Summable.hasSum (((H.indicator {w| j.1=i.1+wrap n w})).congr fun w=>by simp [Set.indicator]))
lemma Belt.norm_direct (i:Leaf n α)(j:Leaf n β): |direct F n i j|≤ C:= by
  have he:= budget_mono ((G i.2 j.2).unweighted ha) (fun w=> norm_nonneg (if j.1=i.1+wrap n w then F i.2 j.2 w else 0)) (fun w=>?_)
  · exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2
  split; rfl; rw [norm_zero]; positivity
omit G ha
lemma advert {F:Stalk α β}(h:Belt F a C)(z:α)(w:β)(i:Cover) : Real.exp (a*size i)* |F z w i| ≤ C:= budget_single (h z w) i -- parse
end stalk
-- direct converts
omit [Fintype α] in
lemma stick_entry (F : Fan α β 1)(n:Side) : direct (stick F) n=headMatrix (pieces F n):= by
  ext i j; rw [headMatrix_at,pieces,direct_apply,← Equiv.tsum_eq sole]; apply tsum_congr; intro w
  let A:= floated i.1 (Prod.snd ∘ (![j]:Fin 1→_)) w; have hh : (![j]:Fin 1→_)=A ↔ j.1=i.1+wrap n (sole w) := ⟨fun h=>congr_arg Prod.fst (congr_fun h 0), fun h=> funext fun k=>by fin_cases k; exact (Prod.ext h rfl)⟩; refine if_congr hh.symm ?_ rfl; unfold stick; rw [sole.symm_apply_apply]; apply congr_arg (fun z=> F i.2 z w); funext k; fin_cases k; rfl

-- base matrix identity Belt sup pricing at period untouched. useful summability unwrapped representation
section coils
variable {F:Stalk α β} (h:Belt F a C)(ha:0≤a)
-- Up injection BOTH types? lift into tagged vertical rank for zero elsewhere, case method
variable {δ : Type}
def expand (F:Stalk α α)(δ:Type): Stalk (δ⊕α) (δ⊕α):= Sum.elim (fun _=>0) (fun i=>Sum.elim (fun _=>0) (F i))
omit [Fintype α] in
lemma bank {F:Stalk α α}(h:Belt F a C)(δ:Type)(hc:0≤C) : Belt (expand F δ) a C:= by
 intro i j; have hz : Width (α:=Axis) a C (0:Cover→ℝ):= by simpa [Width,SumBudget] using hc
 cases i with | inl=> exact hz | inr i=> cases j with | inl=>exact hz | inr j=>exact h i j
end coils
end YM.AllOrder.Ink
