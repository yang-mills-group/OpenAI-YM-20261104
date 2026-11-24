import YM.FVA2.Wick.Papers
/-! # A joint proof on arbitrarily many boson basis insertions -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Boson
open Function Set Finset Filter MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open FormalOPE.RG10.MultiGauge
open PertExtension.Series.Radial PertExtension.GaussianScore
open scoped BigOperators Topology ContDiff Matrix
variable {E A B J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (e : Module.Basis A ℝ E) [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
local notation "Λ" => Raw (Index A J) ℂ
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product p
local notation "σ" => Poly.encode (J:=J) e
local notation "T" => Permit E

section
omit [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
def coord (i:A) : T := ⟨e.coord i,Papers.linear _⟩
lemma coord_at (i : A) : σ (coord e i) = atLetter (bos i) := by
  classical
  change Inks _ (e.coord i)=_
  apply ext_D; · change (↑(e.coord i 0):ℂ)=0; simp
  unfold Inks; intro j; rw [Poly.ink_linear]; rcases j with j|j|j
  · by_cases h:i=j; · subst h; rw [bos,hear]; simp [eased]
    rw [unheard _ (by simp [bos,Ne.symm h])]; simp [eased,h,show coin (0:ℂ) (A:=Index A J)=0 from funext fun l=> by cases l <;> rfl]
  all_goals rw [unheard _ (by simp [bos])]; simp only [eased,Sum.elim_inr,map_zero,Complex.ofReal_zero]; funext l; cases l <;> rfl
end

variable (f:B→A)(s:Finset B) [DecidableEq B]
def cost (f:B→A)(s:Finset B) : T := ∏ i∈s, coord e (f i)
omit [FiniteDimensional ℝ E] [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma cost_at (x:E) : (cost e f s).val x = Law.product (fun i=>e.coord (f i)) s x:= by
  change ((papers E).val (cost e f s)) x = _
  rw [cost,map_prod,Finset.prod_apply]; rfl
variable [MeasurableSpace E][BorelSpace E]
omit [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] in
lemma erase_form (x:A) : D (bos x) (σ (cost e f s)) = ∑ i∈s, ((e.coord (f i) (e x):ℝ):ℂ) • σ (cost e f (s.erase i)) := by
  let F := cost e f s; let U i:= cost e f (s.erase i); let G (i:B):=e.coord (f i); let a :=e x
  have he : layer a (F.val)= ∑ i∈s,G i a • (U i).val:= by
    funext v
    let g (r:ℝ):= v+r • a
    have ht : HasDerivAt g a 0:=by unfold g; simpa using! (((hasDerivAt_id' (0:ℝ)).smul_const a).const_add v)
    have h0 : g 0=v:= by simp [g];
    have hh : (Law.product G s)=(F.val):=(funext (cost_at e f s)).symm
    have h := Law.diffSum_on G s a v 0; rw [hh,zero_smul,add_zero] at h -- name
    have hr : layer a F.val v=Law.diffSum G s a v := by
      unfold layer; rw (occs:=.pos [1]) [← h0]; exact (((Poly.smooth F).differentiable (by simp) (g 0)).hasFDerivAt.comp_hasDerivAt 0 ht).unique h -- ht result at g0
    rw [hr]; unfold Law.diffSum; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; simp [U,cost_at,G,mul_comm]
  change D (bos x) (ink _ _)=_
  rw [inktip]; change ink _ (layer a F.val)=_; rw [he, ink_sum _ s (fun i _=>show germ (G i a • (U i).val) from (Poly.smooth (U i)).contDiffAt.const_smul (G i a))]; apply Finset.sum_congr rfl; intro i _; exact ink_smul _ ((Poly.smooth (U i)).contDiffAt (x:=0)) _

variable (μ : Measure E)[Measure.IsAddHaarMeasure μ]
variable (b : Law E)
local notation "Q" => bosonMatrix b e
local notation "M" => Fermion.bev Q J
local notation "Ω" => Papers.opening μ b
omit [MeasurableSpace E] [BorelSpace E] μ [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] in
lemma pushLetter (x y:A): Chill M (bos x) (bos y)= Q x y := by unfold Chill Fermion.bev; simp [bos]
omit [MeasurableSpace E] [BorelSpace E] [Fintype A] [DecidableEq A] in
lemma Monitor (v w:A) : Q v w=(↑(b.wick (e.coord v) (e.coord w)):ℂ) := by rw [wick_sym]; rfl
include b μ
omit [DecidableEq A] [DecidableEq J] in
lemma balance : View M (σ (cost e f s))= ( Ω (cost e f s):ℂ) := by
    induction s using Finset.strongInduction with
    | H s ih=>
      by_cases h:s.Nonempty; swap; · obtain rfl:=Finset.not_nonempty_iff_eq_empty.mp h; rw [cost,Finset.prod_empty,Poly.encode_unit,Papers.starts,minView]; simp
      obtain ⟨i,hi⟩:=h
      let S:= s.erase i; let ℓ :=e.coord ∘ f; let w:=f i; let t:=cost e f s; let T':= cost e f S; let U j:=cost e f (S.erase j)
      have hc : Ω t= ∑ j∈S, Ω (U j)* b.wick (ℓ i) (ℓ j) := by
        have hp : t.val= fun x=> Law.product ℓ S x * (ℓ i x):= by funext x; rw [cost_at]; exact (Finset.prod_erase_mul _ _ hi).symm -- unfold S maybe
        change b.average μ t.val= _; rw [hp, b.recursion]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold U; rw [← show (cost e f (S.erase j)).val=Law.product ℓ (S.erase j) from funext (cost_at e f _)]; rfl
      have hp : t= coord e w*T':= (Finset.mul_prod_erase _ _ hi).symm
      change View M (σ t)= (↑(Ω t):ℂ); rw [hc,hp, Poly.encode_product, coord_at,
        ibpV («p»:=sector) (bos w) (Fermion.clear_b Q) (Fermion.sym_b Q (Matrix.IsSymm.ext (fun i j=> wick_sym b e j i))) (Poly.encode_sym e T') (Poly.length e T')]; rw [Fintype.sum_sum_type, Finset.sum_eq_zero (s:=Finset.univ (α:=J ⊕ J)), add_zero]; swap
      · intro j _; simp [Chill,Fermion.bev,bos]
      simp_rw [show ∀ y:A, Chill M (bos w) (Sum.inl y)= _ from fun i=> pushLetter e b w i,
        show ∀ y:A,D (Sum.inl y) (σ T')= _ from fun i=> erase_form e f S i,map_sum, map_smul, smul_eq_mul, Finset.mul_sum]; rw [ Finset.sum_comm,Complex.ofReal_sum ]; apply Finset.sum_congr rfl; intro j hj
      rw [Finset.sum_eq_single (f j)]; · simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,Complex.ofReal_one,one_mul,Complex.ofReal_mul, Monitor]; rw [ih (S.erase j) (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset j S) (Finset.erase_ssubset hi))]; exact mul_comm ..
      · intro a _ ha; simp [Ne.symm ha]
      simp
end YM.FVA2.Wick.Boson
