import YM.FormalOPE.RG10.Wing.Cycle
/-! # Vector fields on formal-channel coefficients, finite torus
 If identifying perturbative data with those from boost station, take full
 gauge vector fields from Wilson regulator. Can use mixed parameter types.
 `kick` uses ALL declared directions positions whether coarse or fine. Keep
 generator-sector conditions.Z.Matrix ages & no masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing
open Function Finset PowerSeries Route HStein
open MvPolynomial (pderiv pderiv_X totalDegree)
open scoped Topology BigOperators Classical
variable {X : Type} [Fintype X]
local notation "K"=> Packet X
local notation "W"=> Channel X
local notation "Δ"=> Derivation ℂ W W

variable {i j k :ℕ} (u:X→ Channel X) (P:Channel X) (p:Packet X)

def kick : Derivation ℂ (Channel X) (Channel X):= ∑ i,u i • journeyD (pderiv i)
def down (j:ℕ) : Derivation ℂ (Packet X) (Packet X):= ∑ i, coeff j (u i) • pderiv i
omit [Fintype X] in
private lemma dawn {A:Type*} [CommSemiring A] [Algebra ℂ A] (p:A)(f: X→ Derivation ℂ A A)(T : Finset X): (∑ i∈T,f i) p=∑ i∈T,f i p:= by
 induction T using Finset.induction_on with
 | empty=>simp
 | insert i T hi ih=> rw [sum_insert hi,sum_insert hi,Derivation.add_apply,ih]
lemma kick_eq : kick u P=∑ i, u i * journeyD (pderiv i) P:= by unfold kick; rw [dawn]; rfl
lemma down_eq : down u j p= ∑ i, coeff j (u i)*pderiv i p:= by unfold down; rw [dawn]; rfl
@[simp] lemma down_axis (a:X) : down u j (MvPolynomial.X a)=coeff j (u a):= by rw [down_eq]; simp [pderiv_X, Pi.single_apply]
lemma projection : coeff j (kick u P)=∑ m∈antidiagonal j,down u m.1 (coeff m.2 P) := by rw [kick_eq,map_sum]; simp_rw [coeff_mul,shelves,down_eq,sum_comm (s:=antidiagonal j) (t:=univ)]; -- inspect
lemma sprouting (x:X) : kick u (sprout x)=u x:= by
 apply PowerSeries.ext; intro j; rw [projection, sum_eq_single_of_mem (j,0) (by simp)]; · simp [sprout]
 rintro ⟨i,h⟩ h1 H; have he : h≠0:= by
    rintro rfl; have hu:i=j:= by simpa using h1
    exact H (by rw [hu]);
 simp [sprout,coeff_C,he]
lemma X_charged : kick u PowerSeries.X=0:= by
 apply PowerSeries.ext; intro t; rw [projection, map_zero]; apply sum_eq_zero; rintro ⟨i,j⟩ h; rw [coeff_X]; split <;> simp
lemma skew {Q₁ Q₂ : Channel X}(he:Through k Q₁ Q₂) : Through k (kick u Q₁) (kick u Q₂):= by intro i hi; rw [projection,projection]; exact sum_congr rfl (fun x hh => by rw [he _ (((show x.2 ≤ i from by have hv:=mem_antidiagonal.mp hh; omega)).trans hi)]) -- inspect
lemma skew_power {Q₁ Q₂ : Channel X}(he:Through k Q₁ Q₂)(t:ℕ): Through k (Cycle.powers (kick u) t Q₁) (Cycle.powers (kick u) t Q₂):= by
 induction t with
 | zero=> exact he
 | succ t ih=> rw [Cycle.newDay,Cycle.newDay]; exact skew u ih
lemma leftQuiet (i:ℕ) (he:∀ j < i,coeff j P=0): coeff i (kick u P)=down u 0 (coeff i P) := by
 rw [projection,sum_eq_single_of_mem (0,i) (by simp [mem_antidiagonal])];
 intro x hx h; rw [he x.2 (by
    refine lt_of_le_of_ne (show x.2 ≤ i from by have hv:=mem_antidiagonal.mp hx;omega) (fun h'=> h (Prod.ext ?_ h')) ; have hy := mem_antidiagonal.mp hx; simp; omega), map_zero]

variable (hv : ∀ i, Guard (u i) k 1) (d:ℕ)
local notation "l"=> Primitives.GCC.LocalPolynomial.length
include hv
lemma titled (hi:i+j≤k)(h : totalDegree p ≤ d+3*j): totalDegree (down u i p) ≤ d+3*(i+j):= by
 rw [down_eq]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro a _;
 rw [resolves p,map_sum, mul_sum]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro y hy;
 rw [Derivation.map_smul,chop]; by_cases h':a∈ y.support
 · apply (MvPolynomial.totalDegree_mul ..).trans; refine le_trans (Nat.add_le_add (hv a i (by omega)) ((MvPolynomial.totalDegree_smul_le ..).trans ((MvPolynomial.totalDegree_smul_le ..).trans (show totalDegree (glyph (y-Finsupp.single a 1)) ≤ l (y-Finsupp.single a 1) from MvPolynomial.totalDegree_monomial_le ..)))) ?_
   have ht := (show l y ≤ totalDegree p from MvPolynomial.le_totalDegree hy).trans h; have hy:= distill h'; omega
 rw [Finsupp.notMem_support_iff.mp h',Nat.cast_zero,zero_smul, smul_zero, mul_zero]; simp
lemma closed (H : Guard P k d) : Guard (kick u P) k d:= by
 intro i hi; rw [projection]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro x hx
 rw [←mem_antidiagonal.mp hx] -- inspect
 exact titled u _ hv d ((mem_antidiagonal.mp hx).symm ▸ hi) (H _ ((show x.2 ≤ i from by have hv:=mem_antidiagonal.mp hx;omega).trans hi))
lemma closed_powers (H: Guard P k d) (v:ℕ) : Guard (Cycle.powers (kick u) v P) k d:= by
 induction v with
 | zero=> exact H
 | succ v ih=>rw [Cycle.newDay]; exact closed u _ hv d ih
end YM.FormalOPE.RG10.Wing
