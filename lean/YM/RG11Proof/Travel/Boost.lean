import YM.RG11Proof.Scale.Limits

/-!
# Fixed-coefficient scaling transport: triangular system

The infinitesimal CS in the direction of **shrinking** distances, with
bulk power already factored. β vanishes through linear part, frame generator
R begin no constant (use b with R=-b). Hence iteration raises order, and
the formal-coefficient evolution exists on all s, each coefficient a
polynomial of log. Doesn't pay a cost on actual g, and doesn't validate such
a flow on actual correlators with unannounced growth of ratio, phase etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Travel
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped BigOperators Classical Topology
variable {J:Type*}[Fintype J]

local notation "ps"=>PowerSeries ℝ
structure Static (J:Type*)[Fintype J] where
  β:ps
  b:Square J ps
  quiet : ∀ i≤1,coeff i β=0
  still : piece 0 b=0
namespace Static
variable (K:Static J)

def throws(p:J→ps)(i:J):ps:= K.β*derivative ℝ (p i)+∑ j,K.b i j*p j

def T : (J→ps)→ₗ[ℝ](J→ps) where
   toFun:=K.throws
   map_add':=by intro x y; funext i; simp [throws,mul_add,Finset.sum_add_distrib]; ring
   map_smul':=by
     intro z x; funext i; change K.β*derivative ℝ (z • x i)+(∑ y,K.b i y*(z • x y))= z • K.throws x i
     have hh:derivative ℝ (z • x i) = z • derivative ℝ (x i) := by ext i; simp [coeff_derivative]
     rw [hh]; simp only [ mul_smul_comm,←Finset.smul_sum,←smul_add]; rfl

theorem boost {p q:J→ps}{k}(h:∀ u n, n<k → coeff n (p u)=coeff n (q u))(i:J):coeff k (K.throws p i)=coeff k (K.throws q i):=by
   unfold throws; simp_rw [map_add,map_sum,coeff_mul, coeff_derivative]
   congr 1
   · apply Finset.sum_congr rfl; intro z hz; have hv:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
     by_cases ht:z.1≤1
     · simp [K.quiet z.1 ht]
     rw [h _ _ (by omega)]
   apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro z hz; have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
   by_cases hu:z.1=0
   · simp only [hu,←piece_apply (A:=K.b),K.still,Matrix.zero_apply,zero_mul]
   rw [h _ _ (by omega)]

-- finite exponential in scale s at coefficient k. k fixed, ordinary convention.

def rotor (p:J→ps)(k:ℕ)(s:ℝ): J→ps:= ∑ i∈Finset.range (k+1), (s^i/i.factorial:ℝ) • ((K.T^[i]) p)

def curve (p:J→ps)(s:ℝ)(j:J):ps:=PowerSeries.mk fun k=>coeff k (K.rotor p k s j)

 theorem rotor_support (p:J→ps){i k:ℕ}(h:k < i)(j:J): coeff k ((K.T^[i]) p j) = 0:= by
   induction i generalizing k j with
   |zero=>omega
   |succ i ih=>
      rw [Function.iterate_succ_apply']
      change coeff k (K.throws _ j)=0
      rw [K.boost (q:=0) (fun b n hn=>?_) j]
      · change coeff k (K.T 0 j)=_; rw [map_zero]; exact map_zero _
      simp only [Pi.zero_apply,map_zero]; exact ih (k:=n) (by omega) b

@[simp] theorem finite_eq (p:J→ps)(s:ℝ)(j:J)(k:ℕ): coeff k (K.curve p s j)=coeff k (K.rotor p k s j):=by simp [curve]

@[simp] theorem starts (p:J→ps): K.curve p 0=p:=by
    ext j k; rw [finite_eq]
    unfold rotor; rw [Finset.sum_eq_single_of_mem 0 (by simp) (fun b hb h=>by rw [zero_pow h,zero_div,zero_smul])]; simp

 theorem reach (p:J→ps)(n:ℕ)(s:ℝ)(j:J): Through n (K.curve p s j) (K.rotor p n s j):=by
    intro i hi
    simp_rw [finite_eq,rotor,Finset.sum_apply,map_sum,Pi.smul_apply, map_smul]
    refine Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hi 1)) (fun b _ hb=>?_)
    simp only [Finset.mem_range] at hb
    rw [K.rotor_support p (by omega),smul_zero]

 theorem solutions (p:J→ps)(s:ℝ)(j:J)(k:ℕ):
    HasDerivAt (fun u:ℝ=>coeff k (K.curve p u j)) (coeff k (K.T (K.curve p s) j)) s:=by
    simp_rw [finite_eq,rotor,Finset.sum_apply,map_sum,Pi.smul_apply,map_smul,smul_eq_mul]
    let V (i:ℕ):=coeff k ((K.T^[i]) p j)
    have he (i:ℕ):HasDerivAt (fun u:ℝ=> u^i / i.factorial * V i) ((i*s^(i-1))/(i.factorial:ℝ)*V i) s:=by
      simpa using (((hasDerivAt_pow i s).div_const (i.factorial:ℝ)).mul_const (V i))
    have ht:=HasDerivAt.fun_sum (u:=Finset.range (k+1)) (fun i _=>he i)
    convert! ht using 1
    change coeff k (K.throws _ _)=_
    rw [K.boost (q:=K.rotor p k s) (fun u b hb=> K.reach p k s u b hb.le) j]
    change coeff k (K.T (K.rotor p k s) j)=∑ i∈Finset.range (k+1),(i * s^(i-1))/(i.factorial:ℝ) * V i
    unfold rotor; simp_rw [map_sum,Finset.sum_apply,map_sum,map_smul,Pi.smul_apply,map_smul,smul_eq_mul]
    rw [Finset.sum_range_succ,←Function.iterate_succ_apply' (f:=(K.T: (J→ps)→(J→ps))),K.rotor_support (k:=k) p (by omega),mul_zero,add_zero]
    conv_rhs=> rw [Finset.sum_range_succ' (n:=k)]; simp
    apply Finset.sum_congr rfl; intro i hi
    rw [Nat.factorial_succ]; simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul, V,Function.iterate_succ_apply']
    field_simp
end Static
end YM.RG11.Travel
