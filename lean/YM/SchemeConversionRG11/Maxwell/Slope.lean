import YM.SchemeConversionRG11.Maxwell.Glints

/-! # Joint coefficient at an ordinary crossing of two divisisors, after explicit clearing -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Set
open MvPolynomial
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} {n k l : ℕ} {a y : Fin n} (x : Fin n → Space)

def varied (z : Space) : Script →ₐ[ℂ] Script := aeval fun i ↦ X i - C (z i)
lemma varied_at (p : Script) (x y : Space) : aeval x (varied y p)=aeval (x-y) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [varied]
  | add _ _ hp hq => simp only [map_add,hp,hq]
  | mul_X p i h => rw [map_mul,map_mul,map_mul,h]; simp [varied]

def DD (M : Fin n → ℕ) := ∏ i, varied (x i) chart ^ M i
abbrev Strays (a y : Fin n) := (Finset.univ.erase a).erase y

def extDD (M : Fin n → ℕ) (a y : Fin n) := ∏ i∈Strays a y, varied (x i) chart ^ M i

lemma DD_add (M L : Fin n → ℕ) : DD x (M+L)= DD x M*DD x L := by simp only [DD,Pi.add_apply,pow_add,Finset.prod_mul_distrib]
lemma ext_add (M L : Fin n → ℕ) : extDD x (M+L) a y= extDD x M a y*extDD x L a y := by simp only [extDD,Pi.add_apply,pow_add,Finset.prod_mul_distrib]
lemma DD_ne (M : Fin n→ℕ) (b : Space) (h : ∀ i,sq (b-x i)≠0) : aeval b (DD x M)≠0 := by
  unfold DD; rw [map_prod]; refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_; rw [map_pow,varied_at,chart_at]; exact pow_ne_zero _ (h i)
lemma ext_ne (M : Fin n → ℕ) (d : Space) (h : Blip x a y d) : aeval (d+x a) (extDD x M a y)≠0 := by
  unfold extDD; rw [map_prod]; refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
  rw [map_pow,varied_at,chart_at,show d+x a-x i=d-(x i-x a) by abel]
  exact pow_ne_zero _ (h.across i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1) (Finset.mem_erase.mp hi).1)
lemma DD_decomp (M : Fin n → ℕ) (h : a ≠ y) : DD x M=
    varied (x a) chart ^ M a * varied (x y) chart ^ M y * extDD x M a y := by
  unfold DD extDD
  let Q i := varied (x i) chart ^ M i
  change ∏ i,Q i = Q a * Q y * ∏ i∈_, Q i
  rw [mul_assoc, Finset.mul_prod_erase (Finset.univ.erase a) _ (by simp [Ne.symm h]), Finset.mul_prod_erase _ _ (Finset.mem_univ _)]

def slide (b d v : Space) : Script →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := aeval fun i ↦ C (b i)+X 1*C (d i)+X 0*C (v i)
lemma slide_at (p : Script) (b d v : Space) (z : Fin 2 → ℂ) : aeval z (slide b d v p) = aeval (b+z 1 • d+z 0 • v) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [slide]
  | add _ _ hp hq => simp only [map_add,hp,hq]
  | mul_X p i h => rw [map_mul,map_mul,map_mul,h]; simp [slide,mul_comm]

def fling (d : Space) (a y : Fin n) : Script →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := slide (d+x a) d (d-(x y-x a))
def jumble (d : Space) (a y : Fin n) : ℂ := 2 * dot d (d-(x y-x a))
lemma fling_eval (d : Space) (p : Script) : aeval (0:Fin 2 → ℂ) (fling x d a y p)=aeval (d+x a) p := by
  unfold fling; rw [slide_at]; simp
lemma fling_first (d : Space) (h : Blip x a y d) : fling x d a y (varied (x a) chart) = X 0 * (C (jumble x d a y)*(1+X 1)) := by
  apply MvPolynomial.funext; intro z; change aeval z _=aeval z _
  let v := d-(x y-x a)
  rw [fling,slide_at,varied_at,chart_at,map_mul,map_mul,map_add,map_one,aeval_X,aeval_X,aeval_C]
  rw [show d+x a+z 1 • d+z 0 • (d-(x y-x a))-x a=(1+z 1) • d+z 0 • v by rw [add_smul,one_smul]; unfold v; abel,sq_add,sq_scale,sq_scale,h.first,(show sq v=0 from h.second), dot_scale,dot_scale']
  change _ = _*(2*dot d v*(1+z 1)); ring
lemma fling_second (d : Space) (h : Blip x a y d) : fling x d a y (varied (x y) chart) = X 1 * (C (jumble x d a y)*(1+X 0)) := by
  apply MvPolynomial.funext; intro z; change aeval z _=aeval z _
  let v := d-(x y-x a)
  rw [fling,slide_at,varied_at,chart_at,map_mul,map_mul,map_add,map_one,aeval_X,aeval_X,aeval_C]
  rw [show d+x a+z 1 • d+z 0 • (d-(x y-x a))-x y=z 1 • d+(1+z 0) • v by rw [add_smul,one_smul]; unfold v; abel,sq_add,sq_scale,sq_scale,h.first,(show sq v=0 from h.second), dot_scale,dot_scale']
  change _ = _*(2*dot d v*(1+z 0)); ring

def pick (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b
lemma rising (d : Space) (h : Blip x a y d) (hp : a ≠ y) (L : Fin n → ℕ) (p : Script) : ∃ w : MvPolynomial (Fin 2) ℂ,
    fling x d a y (DD x L*p) = MvPolynomial.monomial (pick (L a) (L y)) 1 * w ∧
    coeff 0 w=jumble x d a y ^ L a * jumble x d a y ^ L y * aeval (d+x a) (extDD x L a y)*aeval (d+x a) p := by
  let F := fling x d a y
  let c := jumble x d a y
  let w := (C c*(1+X (1:Fin 2)))^L a * (C c*(1+X (0:Fin 2)))^L y * F (extDD x L a y)*F p
  refine ⟨w,?_,?_⟩
  · rw [DD_decomp x L hp,map_mul,map_mul,map_mul,map_pow,map_pow,fling_first x d h,fling_second x d h,
      show MvPolynomial.monomial (pick (L a) (L y)) (1:ℂ)= X 0^L a*X 1^L y by rw [X_pow_eq_monomial,X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]; rfl]
    unfold w F c; simp only [mul_pow]; ring
  calc
    _ = aeval (0 : Fin 2 → ℂ) w := (aeval_zero' _).symm -- check
    _ = _ := by unfold w F c; simp only [map_mul,map_pow,map_add,map_one,aeval_X,aeval_C,Pi.zero_apply, add_zero,Algebra.algebraMap_self,RingHom.id_apply,mul_one,fling_eval]

/-- exact leading joint coefficient; only valid under explicit inequalities, no claim
about subdominant Laurent terms. -/
lemma radiates {M L : Fin n → ℕ} (d : Space) (h : Blip x a y d) (ha : a≠y)
    (k l : ℕ) (hk : k ≤ M a) (hl : l ≤ M y) (hM : L ≤ M) (p : Script)
    (he : p=0 ∨ L a<k ∨ L y<l ∨ L a=k ∧ L y=l) :
    MvPolynomial.coeff (pick (M a-k) (M y-l)) (fling x d a y (DD x (M-L)*p))=
      jumble x d a y ^ (M a-k) * jumble x d a y ^ (M y-l) * aeval (d+x a) (extDD x M a y) *
        (if L a=k ∧ L y=l then aeval (d+x a) p/aeval (d+x a) (extDD x L a y) else 0) := by
  classical
  obtain ⟨w,hw,hW⟩ := rising x d h ha (M-L) p
  by_cases H : L a=k ∧ L y=l
  · have hh : M-L+L=M := funext fun i ↦ tsub_add_cancel_of_le (hM i)
    rw [hw, coeff_monomial_mul', Pi.sub_apply, Pi.sub_apply,if_pos H,H.1,H.2,if_pos le_rfl,
      tsub_self,hW]; simp only [Pi.sub_apply,H.1,H.2]
    rw [show extDD x M a y=extDD x (M-L) a y * extDD x L a y from (ext_add (a:=a) (y:=y) x (M-L) L) ▸ congr_arg (fun M ↦ extDD x M a y) hh.symm,map_mul]
    field_simp [ext_ne x L d h]
    rw [mul_div_cancel_right₀ _ (ext_ne x L d h)]
  rw [if_neg H,mul_zero]; rcases he with rfl|he
  · simp
  rw [hw,coeff_monomial_mul', if_neg ?_]
  intro hh
  rcases he with hf|hf|hf
  · have hu := hh 0; simp [pick] at hu; omega
  · have hu := hh 1; simp [pick] at hu; omega
  exact H hf

end YM.SchemeConversionRG11.Corona
