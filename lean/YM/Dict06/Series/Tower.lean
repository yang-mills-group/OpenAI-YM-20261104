import YM.Dict06.Series.Smooth

/-! Finite coefficient composition on homogeneous packets before RG
normalization. No analytic continuation radius required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Series
open Function Filter Tensor Work.G05
open scoped Topology ContDiff BigOperators Classical
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma monomial (n k : ℕ) (v : F) :
    ordinary n (fun t:ℝ=>t^k • v)= if n=k then v else 0 := by
  rw [ordinary,iteratedDeriv_smul_const (show ContDiffAt ℝ n (fun t:ℝ=> t^k) 0 from contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst k; rw [smul_smul,inv_mul_cancel₀ (show (n.factorial:ℝ)≠0 by positivity),one_smul]
  simp
lemma lookup {I:Finset ℕ} (n:ℕ) (v:ℕ→F) :
    ordinary n (fun t:ℝ=>∑ k∈I,t^k • v k) = if n∈I then v n else 0 := by
  rw [ordinary_sum I (fun k (t:ℝ)=>t^k • v k) n (fun k _=> (contDiffAt_id.pow k).smul contDiffAt_const)]
  simp_rw [monomial]
  simp

/-- Finite Taylor terms of f at zero with *ordinary* convention.
Alias used to separate homogeneous operations from analytic functions.
-/
def term (f : D→E) (n : ℕ) : D → E := diagonal (coeff f n 0)
@[simp] lemma term_zero (f : D→E) (x : D) : term f 0 x = f 0 :=
  Tensor.coeff_apply_zero ..
lemma homogeneous_term {k:ℕ} (T : Tensor.T D E k) (n : ℕ) : term (diagonal T) n = if n=k then diagonal T else 0 := by
  funext x; unfold term
  simp_rw [show (ite (n=k) (diagonal T) 0) x = if n=k then diagonal T x else 0 from by split_ifs <;> rfl]
  rw [← radial_eq _ (Tensor.diag_smooth T _).contDiffAt]; simp_rw [Tensor.homogeneous,monomial]
lemma homogeneous_jets {k n : ℕ} (T : Tensor.T D E k) (hne : n≠k) :
    iteratedFDeriv ℝ n (diagonal T) 0=0 := by
  have H : Tensor.coeff (diagonal T) n 0=0 := by
    refine Tensor.ext_diag _ _ (Tensor.coeff_symm (Tensor.diag_smooth T n).contDiffAt) (by simp [Tensor.Sym]) ?_
    rw [← term, homogeneous_term T,if_neg hne]
    rfl
  unfold Tensor.coeff at H
  exact (smul_eq_zero.mp H).resolve_left (show (n.factorial:ℝ)⁻¹ ≠0 by positivity)

lemma truncate_inner (n : ℕ) {f : D→E} {g : E→F}
    (hf:ContDiffAt ℝ n f 0)(hg:ContDiffAt ℝ n g (f 0)) (j:ℕ) (h:j≤n) :
    term (g ∘ f) j = term (g ∘ blockTaylor n f) j := by
  have he : blockTaylor n f 0=f 0:= blockTaylor_zero n f
  unfold term Tensor.coeff
  rw [jets_comp (g:=g) (g':=g) hf (blockTaylor_contDiff n f _).contDiffAt hg (he ▸ hg) he.symm
    (fun k hk=>(blockTaylor_jets hf k hk).symm) (fun _ _=>rfl) j h]
lemma truncate_outer (n : ℕ) {f : D→E} {g : E→F}
    (hf:ContDiffAt ℝ n f 0)(hg:ContDiffAt ℝ n g 0) (he:f 0=0) (j:ℕ) (h:j≤n) :
    term (g ∘ f) j = term (blockTaylor n g ∘ f) j := by
  have hg' : ContDiffAt ℝ n g (f 0):=by simpa only [he]
  unfold term Tensor.coeff
  rw [jets_comp hf hf hg' (blockTaylor_contDiff n g _).contDiffAt rfl (fun _ _=>rfl)
    (by intro i hi; rw [he, blockTaylor_jets hg i hi]) j h]

variable {k : ℕ}

/-- Full composition of a homogeneous k-linear packet with a common
*zero-constant* argument germ, evaluated on a ray. With ℕ-valued profiles
in the list there are no implicit permutations or symmetry divisors; even
when T is symmetric this uses all ordered slots.
-/
lemma homogeneous_comp (T : Tensor.T E F k) {L : D→E} {l : ℕ}
    (hL : ContDiffAt ℝ l L 0) (h0 : L 0=0) (x : D) :
    term (diagonal T ∘ L) l x =
      let r := (Finset.range (l+1)).erase 0
      ∑ s ∈ Fintype.piFinset (fun _ : Fin k => r),
        if l=∑ i, s i then T (fun i=>term L (s i) x) else 0 := by
  rw [truncate_inner l hL (Tensor.diag_smooth T _).contDiffAt l le_rfl]
  let B := blockTaylor l L
  change term (diagonal T ∘ B) l x = _
  unfold term; rw [← radial_eq _ ((Tensor.diag_smooth T l).comp (blockTaylor_contDiff ..)).contDiffAt]
  let r := (Finset.range (l+1)).erase 0
  let a (i:ℕ) := term L i x
  have he t : B (t • x) = ∑ i∈r, (t:ℝ)^i • a i := by
    change blockTaylor l L _=_; rw [blockTaylor,Finset.sum_apply]; simp_rw [Tensor.homogeneous]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (show 0<l+1 by omega)), show diagonal (Tensor.coeff L 0 0) x=0 from (term_zero L x).trans h0, smul_zero,add_zero]; rfl

  let S := Fintype.piFinset (fun _ : Fin k => r)
  have expand_at t : (diagonal T ∘ B) ((t:ℝ) • x) = ∑ s∈S,
        t^(∑ i,s i) • T (fun i=>a (s i)) := by
    rw [Function.comp_apply,he]; unfold diagonal
    rw [T.map_sum_finset (fun (_ : Fin k) (j :ℕ)=>t^j • a j) (fun _=>r)] -- parameter
    refine Finset.sum_congr rfl fun s _=> ?_
    rw [show (T fun i => t ^ s i • a (s i))=_ from T.map_smul_univ (fun i=>t^s i) (fun i=>a (s i)), Finset.prod_pow_eq_pow_sum]
  change (ordinary l fun t=> (diagonal T ∘ B) (t • x))=_
  rw [funext expand_at,ordinary_sum S (fun s (t:ℝ)=>t^(∑ i,s i) • T (fun i=>a (s i))) _ (fun _ _=>(contDiffAt_id.pow _).smul contDiffAt_const)]
  exact Finset.sum_congr rfl fun s _=>monomial ..

lemma early (T : Tensor.T E F k) {L : D→E} {l:ℕ} (h:l<k) (hl:ContDiffAt ℝ l L 0) (h0:L 0=0) :
    term (diagonal T ∘ L) l = 0 := by
  funext x; rw [homogeneous_comp T hl h0]; apply Finset.sum_eq_zero; intro s hs
  refine if_neg ?_; push Not
  have hp i : 1 ≤ s i:= by
    have he: s i≠0 := Finset.ne_of_mem_erase (Fintype.mem_piFinset.mp hs i)
    omega
  have he:= Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin k => 1) (g:=s) (fun i _=>hp i); simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at he
  omega
lemma first_hit (T : Tensor.T E F k) {L : D→E} (hl:ContDiffAt ℝ k L 0) (h0:L 0=0) (x : D) :
    term (diagonal T ∘ L) k x = diagonal T (term L 1 x) := by
  cases k with
  | zero => exact (term_zero _ _).trans (congrArg T (Subsingleton.elim _ _))
  | succ k=>
    rw [homogeneous_comp T hl h0]
    dsimp only []
    rw [Finset.sum_eq_single (fun _=>1)]
    · simp; rfl -- try
    · intro s hs he
      refine if_neg ?_; intro hh; apply he
      have hv (i) : 1 ≤ s i := by
        have hp:=Finset.ne_of_mem_erase (Fintype.mem_piFinset.mp hs i)
        omega
      have hc : ∑ i, ((s i)-1) = 0 := by
        have he' : ∑ i, s i=∑ i, ((s i)-1+1) := Finset.sum_congr rfl fun i _=> (Nat.sub_add_cancel (hv i)).symm
        rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at he'
        omega
      funext i
      have hp: s i-1=0:= (Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)).mp hc i (Finset.mem_univ _); change s i = 1
      specialize hv i; omega
    · intro hn; exact False.elim (hn (Fintype.mem_piFinset.mpr (fun _ => Finset.mem_erase.mpr ⟨by decide,Finset.mem_range.mpr (by omega)⟩)))

lemma term_one (L : D→E) (x:D): term L 1 x=fderiv ℝ L 0 x:=by
  unfold term diagonal Tensor.coeff; rw [smul_apply, iteratedFDeriv_one_apply]; simp

lemma termGerm (l:ℕ) (f g : D→E) (h : f =ᶠ[𝓝 0] g) : term f l=term g l:=by unfold term; rw [GermCoeff l h]
lemma term_sum {I:Type*} (s:Finset I) (f:I→D→E) (l:ℕ)
    (h:∀ i∈s,ContDiffAt ℝ l (f i) 0):
    term (fun t=>∑ i∈s,f i t) l=∑ i∈s,term (f i) l := by
  unfold term
  rw [funext (fun t=> (Finset.sum_apply t s f).symm),Tensor.coeff_sum l 0 f s h]
  funext x; simp [Tensor.diagonal]
lemma comp (f : E→F) (L : D→E) (n : ℕ) (hL : ContDiffAt ℝ n L 0) (hf:ContDiffAt ℝ n f 0) (h0:L 0=0)
    (x:D) : term (f ∘ L) n x = ∑ i∈Finset.range (n+1), term (term f i ∘ L) n x := by
  rw [truncate_outer n hL hf h0 n le_rfl,
      show blockTaylor n f ∘ L = fun y=>∑ i∈Finset.range (n+1),(term f i ∘ L) y from
        funext (fun y=>Finset.sum_apply (L y) (Finset.range (n+1)) (term f)),term_sum (Finset.range (n+1)) (fun i=>term f i ∘ L) n (fun i _ => (Tensor.diag_smooth _ _).contDiffAt.comp _ hL),Finset.sum_apply]
end YM.Dict06.Series
