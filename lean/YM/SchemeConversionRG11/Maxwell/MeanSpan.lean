import YM.SchemeConversionRG11.Maxwell.MeanPoly

/-! # Finish ball moment tests -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Tensor Set MvPolynomial
open scoped Topology BigOperators RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def beamL : Bean ι →ₗ[ℝ] ShellBook ι where
  toFun := laser
  map_add' p q := laser_add p q
  map_smul' t p := (laser_smul t p).trans (IsScalarTower.algebraMap_smul ℂ t _)

def beamsL (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n ↦ Bean ι) (ShellBook ι) :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin n) (ShellBook ι)).restrictScalars ℝ |>.compLinearMap fun _ ↦ beamL

def logs (A : ShellBook ι →ₗ[ℂ] ℂ) (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n ↦ Bean ι) ℂ := (A.restrictScalars ℝ).compMultilinearMap (beamsL n)
lemma logs_cost (A : ShellBook ι →ₗ[ℂ] ℂ) (v : Fin n → Bean ι) : logs A n v=A (∏ i,laser (v i)) := rfl
lemma logs_route (A : ShellBook ι →ₗ[ℂ] ℂ) : Continuous (logs A n) := by
  classical
  let L := logs A n
  have hi (v : Bean ι) : v = ∑ i : ι, v i • bat i := by ext1 i; simp [bat,Pi.single_apply]
  have hh (v : Fin n → Bean ι) : L v= ∑ q : (Fin n → ι),(∏ i : Fin n,v i (q i)) • L (bat ∘ q) := by
    conv_lhs => rw [show v=fun i : Fin n ↦ ∑ j,v i j • bat j from funext fun i ↦ hi _]
    rw [L.map_sum_finset _ (fun _ ↦ Finset.univ)]; simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun q _ ↦ ?_; exact L.map_smul_univ _ _
  change Continuous (L: (Fin n→Bean ι)→ℂ)
  rw [funext hh]; apply continuous_finsetSum; intro i _
  have he : Continuous (fun a : Fin n → Bean ι ↦ ∏ k,(a k).ofLp (i k)) := continuous_finsetProd _ fun j _ ↦
    (EuclideanSpace.proj (i j) (𝕜:=ℝ)).continuous.comp (continuous_apply j)
  exact he.smul continuous_const

def attune (A : ShellBook ι →ₗ[ℂ] ℂ) (n : ℕ) : T (Bean ι) ℂ n := ⟨logs A n,logs_route A⟩
lemma attune_sym (A : ShellBook ι →ₗ[ℂ] ℂ) (n : ℕ) : Tensor.Sym (attune A n) := fun v s ↦ by
  change logs A n _ = logs A n v; rw [logs_cost,logs_cost]; congr 1; exact Fintype.prod_equiv s _ _ fun _ ↦ rfl

variable (r : ℝ) (i : ι)
lemma attunes {M : ℕ} (h : n≤M) : attune (mean ι r) n=attune (roundMean r i M) n := by
  apply Tensor.ext_diag _ _ (attune_sym _ n) (attune_sym _ n); funext x
  change logs _ n (fun _ ↦ x) = logs _ n (fun _ ↦ x)
  rw [logs_cost,logs_cost]; simp only [Finset.prod_const,Fintype.card_fin,Finset.card_univ]; exact (round_at r x i M h).symm

lemma burns_forever (p : ShellBook ι) : ∃ n, ∀ m ≥ n, mean ι r p=roundMean r i m p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨b,hb⟩ := hp; obtain ⟨c,hc⟩ := hq; exact ⟨b+c,fun m hm ↦ by rw [map_add,map_add,hb m (by omega),hc m (by omega)]⟩
  | monomial p a =>
    obtain ⟨L,hL,_,_⟩ := mon_list p
    simp only [MvPolynomial.coe_basisMonomials] at hL
    have he (q : List ι) : (q.map (MvPolynomial.X (R:=ℂ))).prod= ∏ k:Fin q.length, laser (bat (q.get k)) := by
      simp_rw [laser_atom, ← List.prod_ofFn, show (fun k=> X (R:=ℂ) (q.get k))=MvPolynomial.X ∘ q.get from rfl, ←List.map_ofFn,List.ofFn_get]
    refine ⟨L.length,fun m hm ↦ ?_⟩
    rw [show (monomial p a)=a • monomial p (1:ℂ) by simp [MvPolynomial.smul_monomial],map_smul,map_smul,hL,he]
    exact congr_arg (a • ·) (congr_arg (fun P:T (Bean ι) ℂ L.length ↦ P fun j ↦ bat (L.get j)) (attunes r i hm))
include i in
lemma ballMean_test {p : ShellBook ι} (h : ∀ j : ℕ,melt j p=0) : mean ι r p=0 := by
  obtain ⟨m,hm⟩ := burns_forever r i p
  rw [hm m le_rfl,roundMean,LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro b _; rw [LinearMap.smul_apply,h,smul_zero]

variable {G : Gauge} {σ : Type*} [Fintype σ]

lemma snowfall (C₀ : G.ColorIndex) (p : σ→ℂ) (W : Panel σ n G) (h : Muted p W) (A : Fin n→ TaylorTower G) :
    mean (Pct G) r (snow p W A)=0 := by classical exact ballMean_test r (C₀,C₀) (fun j ↦ powered C₀ j h A)

end YM.SchemeConversionRG11.Corona
