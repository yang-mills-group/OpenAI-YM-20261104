import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Pairs
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The actual formal coupling shift

Any order formula via finite substitution coefficients from logs.
 Uses convolution diagrams; no estimates. Need ratio cost for analytic later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Convolve
open PowerSeries (coeff)
abbrev Cn := PowerSeries ℂ
variable {P Q R : Type*}[AddCommGroup P][Module ℂ P][AddCommGroup Q][Module ℂ Q][AddCommGroup R][Module ℂ R]
    {c d : Cn} {U:T P} {n m : ℕ}
abbrev Rooted (c:Cn) := coeff 0 c=0
abbrev cut (c:Cn)(i j:ℕ):= coeff j (c^i)
lemma blocked (h:Rooted c){i j:ℕ}(ht:i>j): cut c i j=0:= by
    induction i generalizing j with
    | zero=>omega
    | succ i ih=> unfold cut; rw [pow_succ,PowerSeries.coeff_mul]; refine Finset.sum_eq_zero fun x hx=>?_; obtain hh:=mem_antidiagonal.mp hx; by_cases hz:x.2=0; swap; · rw [show coeff x.1 (c^i)=0 from ih (by omega),zero_mul]
                  rw [hz,h,mul_zero] -- Rooted def
lemma root_first (h:Rooted c)(he:coeff 1 c=1)(i:ℕ): cut c i i=1:= by
    induction i with
    | zero=>unfold cut; simp
    | succ i ih=> unfold cut; rw [pow_succ,PowerSeries.coeff_mul,Finset.sum_eq_single (i,1)]; simp only [he]; exact (mul_one _).trans ih
                  · intro x hx hv; obtain hh:=mem_antidiagonal.mp hx; by_cases he:x.2=0; rw [he,h,mul_zero]; have ht:x.1< i:= by contrapose! hv; exact Prod.ext (by dsimp; omega) (by dsimp; omega)
                    rw [show coeff x.1 (c^i)=0 from blocked h ht,zero_mul]
                  simp
lemma clock (c:Cn)(i j k:ℕ): ∑ d ∈ antidiagonal k,cut c i d.1 * cut c j d.2=cut c (i+j) k:= by unfold cut; rw [pow_add,PowerSeries.coeff_mul]

def substitute (c:Cn): T P→ₗ[ℂ] T P where
   toFun f n:= ∑ j∈Finset.Iic n, cut c j n • f j
   map_add' f g:= by ext; simp [Pi.add_apply,smul_add,Finset.sum_add_distrib]
   map_smul' t f:= by ext; simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_comm t]
lemma rules (c:Cn)(F:T P)(n:ℕ): substitute c F n=∑ j∈Finset.Iic n, cut c j n • F j:= rfl
lemma larger (h:Rooted c){i j:ℕ}(hp:i≤j)(F:T P): substitute c F i=∑ k∈Finset.Iic j,cut c k i • F k := by rw [rules]; exact Finset.sum_subset (Finset.Iic_subset_Iic.mpr hp) (fun k hk hm=> by rw [blocked h (by simp_all only [Finset.mem_Iic]; omega),zero_smul]) -- parentheses
lemma pay0 (c:Cn)(F:T P): substitute c F 0=F 0:= by have he : Finset.Iic (0:ℕ)={0}:= Finset.ext (by simp) ; simp [substitute,cut,he]
lemma comm (c:Cn)(F:T P)(L:P→ₗ[ℂ] Q): promote L (substitute c F)=substitute c (promote L F):= by funext i; simp only [rules,promised,map_sum,map_smul]
-- splitting triangular kernel
omit [Module ℂ P] in
lemma price (K: ℕ→ℕ→P) (T:ℕ) (hK:∀ i j,T< i+j→ K i j=0):
   (∑ i∈Finset.Iic T,∑ j∈Finset.Iic T,K i j)= ∑ i∈ Finset.Iic T,∑ j∈ antidiagonal i,K j.1 j.2:= by
    have he i (hi:i≤T): ∑ j∈ Finset.Iic T,K i j=∑ s∈Finset.Iic T,if i≤s then K i (s-i) else 0:= by
       rw [← Finset.sum_filter, ← Finset.sum_subset (Finset.Iic_subset_Iic.mpr (show T-i≤T from by omega)) (fun s hs hs'=> hK i s (by simp_all only [Finset.mem_Iic]; omega))];
       refine Finset.sum_bij (fun i' _=> i'+i) (fun i' hi'=>?_) ?_ ?_ ?_
       · simp_all only [Finset.mem_filter, Finset.mem_Iic]; omega
       · intro _ ha _ hb him; omega
       · intro s hx; rw [mem_filter, Finset.mem_Iic] at hx; exact ⟨s-i,Finset.mem_Iic.mpr (by omega),by omega⟩
       intro i' hi'; simp
    calc
      _ = ∑ i∈Finset.Iic T,∑ j∈Finset.Iic T,if i≤j then K i (j-i) else 0:= Finset.sum_congr rfl fun i hi=> he i (Finset.mem_Iic.mp hi)
      _ = _ := by rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun t ht=>?_); rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:=K)]; rw [← Finset.sum_filter]; congr! 1; ext i; simp; simp only [Finset.mem_Iic] at ht; omega
lemma substitute_pair (h:Rooted c)(F:T P) (G:T Q)(L:P→ₗ[ℂ] Q→ₗ[ℂ] R): pairW L (substitute c F) (substitute c G)= substitute c (pairW L F G):= by
   funext y; rw [paired,rules]
   let Z k j:= L (F k) (G j); let W i j p q:= (cut c p i * cut c q j) • Z p q
   have hh i (hi:i∈antidiagonal y): L (substitute c F i.1) (substitute c G i.2)=∑ k∈Finset.Iic y, ∑ j∈Finset.Iic y,W i.1 i.2 k j:= by
       obtain hp:=mem_antidiagonal.mp hi; rw [larger h (show i.1 ≤ y from by omega),larger h (show i.2≤ y from by omega)]; simp only [map_sum, LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j hj=>Finset.sum_congr rfl fun k hk=>?_ ; unfold W; rw [mul_comm]
   trans ∑ k∈antidiagonal y,∑ i∈Finset.Iic y,∑ j∈Finset.Iic y,W k.1 k.2 i j; · exact Finset.sum_congr rfl hh
   rw [Finset.sum_comm];
   have he i : ∑ k∈antidiagonal y,∑ j∈Finset.Iic y,W k.1 k.2 i j=∑ j∈Finset.Iic y,cut c (i+j) y • Z i j:= by rw [Finset.sum_comm]; unfold W; simp_rw [← Finset.sum_smul,clock]
   simp_rw [he]; rw [price (fun i j=>cut c (i+j) y • Z i j) y (fun i j he=>by rw [blocked h he,zero_smul])]; refine Finset.sum_congr rfl fun i hi=> ?_; rw [paired, Finset.smul_sum]; exact Finset.sum_congr rfl (fun j hj=>by rw [Finset.mem_antidiagonal.mp hj]) -- Z rfl
end YM.MS.Book.Program
