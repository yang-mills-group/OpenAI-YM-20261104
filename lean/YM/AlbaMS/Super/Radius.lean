import YM.AlbaMS.Super.Straight

/-!
# vectors and linear brackets, detection of second-order constant comm
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function
open scoped BigOperators Classical
variable {ι R : Type*} [CommRing R] {ρ:ι→Bool} (p : Bool)
variable {F G I : Coil ρ R} {k K : ι→ι→R} {s : Finset ι} {m n : ℕ} {i j : ι}
variable {U W : Module.End R (Coil ρ R)}

def tom (s : Finset ι)(v : ι→Coil ρ R): Module.End R (Coil ρ R):=∑ i∈s,LinearMap.mul R _ (v i) ∘ₗ D i
lemma tom_apply (s:Finset ι)(v : ι→Coil ρ R)(F : Coil ρ R): tom s v F = ∑ i∈s,v i*D i F:= by simp_rw [tom,LinearMap.sum_apply]; rfl
lemma tom_var (v : ι→Coil ρ R)(i : ι)(h:i∈s): tom s v (varC R ρ i)=v i:= by simp [tom_apply,varD,h]
lemma from_vectors (h:Graded ρ p k): tether p k s F G=tom s (fun i=> cross p k s F (varC R ρ i)) G:=by
  rw [tom_apply];simp_rw [from_tether,from_cross _ _ _ _ _ h]; simp_rw [Finset.sum_mul,smul_mul_assoc]; rw [Finset.sum_comm (f:=fun i j : ι => ∑ u∈s, k j u • (_))] -- move RHS i
  refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.sum_comm (f:=fun x j=> k i j • (_ * D x G))]; refine Finset.sum_congr rfl fun j hj=> ?_
  rw [← Finset.smul_sum]; congr 1; simp [link,varD,add_mul, mul_ite,ite_mul, Finset.sum_add_distrib,hi,hj]

-- scalar from var pair (vac orientation)
lemma touch_pair (hi:i∈s)(hj:j∈s): touch k s (varC R ρ i*varC R ρ j) []= k i j+sting (ρ i && ρ j) (k j i):= by
  have he (a b : ι) : (varC R ρ i* varC R ρ j) [a,b]= (if a=i then if b=j then (1:R) else 0 else 0) + if a=j then if b=i then sting (ρ i && ρ j) (1:R) else 0 else 0 := by
    rw [mul_cons,varD,varD,(var_tone (ρ:=ρ) (R:=R) i).pl]
    congr 1
    · by_cases H:a=i<;> simp [H,var_read]
    by_cases H:a=j; subst a; by_cases ht:b=i<;>simp [ht,var_read,Bool.and_comm]; simp [H]
  rw [touch_apply];simp_rw [sum_read,smul_read,D_read,he,mul_add,mul_ite,mul_one,mul_zero,Finset.sum_add_distrib]; simp [hi,hj,mul_sting]

def Twin (s : Finset ι)(U : Module.End R (Coil ρ R)) :Prop:=∃ k,U=touch k s
namespace Twin
lemma none : Twin s (0:Module.End R (Coil ρ R)):=⟨0,(LinearMap.ext fun i=>by simp [touch_apply]).symm⟩
lemma is (R:Type*) [CommRing R] (s : Finset ι)(k:ι→ι→R):Twin s (touch (ρ:=ρ) k s):=⟨k,rfl⟩
lemma sub (h:Twin s U)(H:Twin s W): Twin s (U-W):=by
  obtain ⟨g,rfl⟩:=h; obtain ⟨k,rfl⟩:=H; refine ⟨g-k,LinearMap.ext fun f=>?_⟩; simp only [touch_apply,LinearMap.sub_apply,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
lemma vacate {i j : ι}(h:Twin s U): U (varC R ρ i*varC R ρ j)=put ρ (U (varC R ρ i*varC R ρ j) []) := by obtain ⟨k,rfl⟩:=h; exact (Cap.touch _ 0 _ _ ((var_cap (R:=R) i).mul (var_cap j))).eroded -- hi,hj unused
lemma zero [Algebra ℚ R](h:Twin s U)(H:∀ i∈s,∀ j∈s,U (varC R ρ i*varC R ρ j) []=0): U=0:=by
  obtain ⟨k,rfl⟩:=h
  have hh (i : ι)(hi:i∈s)(j)(hj:j∈s): k i j= -(sting (ρ i && ρ j) (k j i)):=eq_neg_iff_add_eq_zero.mpr ((touch_pair hi hj).symm.trans (H i hi j hj))
  apply LinearMap.ext; intro i; apply proletariat Nat.zero_lt_two; change (↑(2:ℕ):R) • touch k s i=_ • (0:Coil ρ R); simp only [Nat.cast_ofNat, smul_zero,two_smul]
  have hv : touch k s i=-(touch k s i):=by
    rw [touch_apply]; nth_rw 1 [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj=> Finset.sum_congr rfl fun l hl=> ?_
    rw [hh l hl j hj, DD i j l]; cases ρ l<;>cases ρ j<;>simp
  exact eq_neg_iff_add_eq_zero.mp hv
end Twin
end YM.MSBar.Bric.Coil
