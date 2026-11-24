import YM.Next.RANK.GaussSubst
import YM.Extra.FREE_DETECTOR_ALGEBRA.PowerGram

/-!
# Gaussian contraction algebra (for X-space jets)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Contraction
open Next.Rank.Normal Function Set Finsupp MvPolynomial
open scoped BigOperators Pointwise
variable {ι J: Type*}

abbrev Cov (ι : Type*) := Next.Rank.Normal.Symmetric ι

-- Gaussian contraction never moves a monomial out of its downward closure
variable (b : ι → ℕ)
def weightBound (d : ℕ) : Submodule ℂ (poly ι) := MvPolynomial.restrictSupport ℂ (setOf fun a => Finsupp.weight b a≤d)
lemma bounded {v : poly ι} {d : ℕ} : v∈weightBound b d ↔ ∀ i∈v.support, Finsupp.weight b i≤d := (mem_restrictSupport_iff ..)
lemma higher {d e : ℕ} (h : d≤e):weightBound b d ≤ weightBound b e := MvPolynomial.restrictSupport_mono _ (fun _ hi=> le_trans hi h)
lemma has_self (a : ι →₀ ℕ) (c : ℂ) : monomial a c ∈ weightBound b (weight b a) :=
  (bounded ..).mpr (fun _ hi => (Finset.mem_singleton.mp (support_monomial_subset hi)) ▸ le_rfl)
lemma bounds_mul {v w : poly ι} {d e : ℕ} (h : v∈weightBound b d) (k : w∈ weightBound b e): v*w∈weightBound b (d+e):=by
  classical
  rw [bounded]; intro i hi; obtain ⟨x,hx,y,hy,rfl⟩:= Finset.mem_add.mp (MvPolynomial.support_mul v w hi); rw [map_add]; exact add_le_add ((bounded b).mp h x hx) ((bounded b).mp k y hy)
lemma bound_split (L : Module.End ℂ (poly ι)) (h : ∀ a : ι →₀ ℕ,∀ c, L (monomial a c) ∈ weightBound b (weight b a))
    {p : poly ι} {d : ℕ} (he:p∈weightBound b d) : L p∈weightBound b d :=by
  classical
  rw [p.as_sum,map_sum]; exact Submodule.sum_mem _ (fun a ha=>higher b ((bounded b).mp he a ha) (h _ _))
lemma slit_bound (L : ι → ℂ) {p : poly ι} {d : ℕ} (h : p∈weightBound b d) : slit L p∈ weightBound b d:= by
  classical
  apply bound_split b (slit L).toLinearMap _ h; intro a c; change slit L (monomial a c) ∈ _; rw [slit,mkDerivation_monomial,Finsupp.sum]; apply Submodule.smul_mem _ _; apply Submodule.sum_mem; intro i hi
  rw [smul_eq_mul,mul_comm, MvPolynomial.C_mul']; refine Submodule.smul_mem _ _ (higher b ?_ (has_self b _ _))
  obtain ⟨w,hw⟩:= exists_add_of_le (tsub_le_self (b:=single i 1) (a:=a)); nth_rw 2 [hw]; simp
lemma wick_bound (L : Cov ι) {p : poly ι} {d : ℕ} : p∈ weightBound b d → milk L p ∈ weightBound b d:=by
  apply bound_split; intro a c; apply Extra.FD.per_factor a
  · change milk L (C c)∈ _; rw [fine]; exact has_self b 0 c
  intro w i hx
  rw [monomial_add_single,pow_one,mul_comm,feeds]; apply Submodule.add_mem
  · rw [map_add,add_comm]; exact bounds_mul b (has_self b _ _) hx
  apply higher b _ (slit_bound _ _ hx); rw [map_add]; omega

-- Pullback covariance identities in finite-source Wick operations
lemma treats_add (M : Cov ι) (x y z : ι→₀ℂ) : treats M (x+y) z=treats M x z+treats M y z := by rw [treats_comm,treats,map_add]; exact congr_arg₂ (·+·) (treats_comm M z x) (treats_comm M z y)
lemma treats_single (M : Cov ι) (i j : ι) (v w : ℂ) : treats M (single i v) (single j w)=w*v*M.cov i j :=by
  unfold treats; simp [Pi.smul_apply]; ring
lemma treats_sum (M : Cov ι) {τ : Type*} (f : τ → ι →₀ ℂ) (s : Finset τ) (x : ι →₀ ℂ) : treats M (∑ i∈s,f i) x =∑ i∈s,treats M (f i) x:=by
  classical
  induction s using Finset.induction_on with
  | empty => simp [treats,linearCombination_apply]
  | insert _ _ he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,treats_add,ih]
lemma scope_neg (M : Cov ι) (L : J → ι→₀ℂ): scope L (-M)= -(scope L M):= by
  classical
  apply Next.Rank.Normal.Symmetric.ext; funext i j; change treats (-M) _ _ = -treats M _ _; simp [treats,linearCombination_apply,Finsupp.sum,show (-M).cov = - M.cov from rfl,Finset.sum_neg_distrib]
end YM.XSpace.Contraction
