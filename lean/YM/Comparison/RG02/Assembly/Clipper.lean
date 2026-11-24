import YM.Analysis.Homogeneous
import YM.Comparison.RG02.Affinity.Vibe
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly.Clipper
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open YM.Tensor YM.Analysis
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X→Y} {x : X}
variable (hf : ContDiffAt ℝ ω f 0)

abbrev dz (k:ℕ) (y : X) (f : X→Y) := ((D y)^[k]) f
lemma dz_right (k:ℕ) (y:X) (f : X→Y) : dz (k+1) y f= dz k y (D y f) := Function.iterate_succ_apply ..
include hf
lemma dz_known (k:ℕ) (v:X) : ContDiffAt ℝ ω (dz k v f) 0 := by
   induction k generalizing f with | zero=> exact hf | succ k h=> rw [dz_right]; exact h (dSmooth hf v (by simp))
omit hf in
lemma weight (x:X) (t:ℝ) (n:ℕ) (f:X→Y) : Assembly.jet f n (t • x)= t^n • Assembly.jet f n x := homogeneous (Tensor.coeff f n 0) x t
omit hf in
lemma empty (n : ℕ) (h : n≠0) (f : X→Y) : Assembly.jet f n 0=0 := by
   have ht := weight (0:X) 0 n f; rwa [zero_smul,zero_pow h,zero_smul] at ht
-- iterate line derivative => exact splitting rule
variable (x v : X)
lemma gradient (z : ℝ) (n : ℕ) : HasDerivAt (fun u:ℝ=> Assembly.jet f (n+1) (x+u • v)) (Assembly.jet (D v f) n (x+z•v)) z := by
   let g := Tensor.diagonal (Tensor.coeff f (n+1) 0)
   have hp : ContDiff ℝ ω g := Tensor.diag_smooth ..
   have hb:= hasDerivAt_id' z |>.smul_const v |>.const_add x
   have hh : HasDerivAt (fun u:ℝ => x+u•v) v z:=by simpa using hb
   have ht:= (hp.differentiable (by simp) (x+z • v)).hasFDerivAt.comp_hasDerivAt z hh
   change HasDerivAt (g ∘ _) (Tensor.diagonal (Tensor.coeff (D v f) _ _) _) z
   rw [← Tensor.slot_lower (j:=n) (hf.of_le le_top)]; exact ht

lemma split (z : ℝ) (n : ℕ) : Assembly.jet f n (x+z•v) = ∑ i∈range (n+1), (z^i/(i.factorial:ℝ)) • Assembly.jet (dz i v f) (n-i) x := by
   induction n generalizing z f with
   | zero=> simp [dz]
   | succ n h=>
     let t (i : ℕ) := Assembly.jet (dz i v f) (n+1-i) x
     let g := fun z:ℝ=> ∑ i∈range (n+1+1),(z^i / (i.factorial:ℝ)) • t i
     let k := fun z:ℝ=>∑ i∈range (n+1), (z^i/(i.factorial:ℝ)) • t (i+1)
     have he (z:ℝ):Assembly.jet (D v f) n (x + z • v)= k z:= by
        rw [h (dSmooth hf v (by simp))]; simp_rw [k,t,dz_right]; simp only [Nat.add_sub_add_right]
     have hg (z:ℝ): HasDerivAt g (k z) z := by
        let p(i:ℕ) (z:ℝ) := (z^i/(i.factorial:ℝ)) • t i
        have hh(i:ℕ): HasDerivAt (p (i+1)) ((z^i/(i.factorial:ℝ)) • t (i+1)) z := by
            unfold p
            convert (((hasDerivAt_pow (x:=z) (n:=i+1)).div_const ((i+1).factorial:ℝ)).smul_const (t (i+1))) using 1
            congr 1; rw [Nat.factorial_succ, Nat.cast_mul, show i+1-1=i by omega]; field_simp
        rw [show g= fun z=> ∑ i∈range (n+1),p (i+1) z + t 0 from funext fun z=> (sum_range_succ' (fun i=>p i z) _).trans (by simp [p])]
        exact (HasDerivAt.fun_sum (fun i _=> hh i)).add_const _
     let F₀ (z:ℝ) := Assembly.jet f (n+1) (x+z • v)
     apply (IsOpen.eqOn_of_deriv_eq (f:=F₀) (g:=g) (x:=0) isOpen_univ isPreconnected_univ (fun u _=> (gradient hf x v u n).differentiableAt.differentiableWithinAt) (fun u _=> (hg u).differentiableAt.differentiableWithinAt) ?_ (Set.mem_univ _) ?_) (Set.mem_univ z)
     · intro z hz; exact ((gradient hf x v z n).deriv.trans (he z)).trans (hg z).deriv.symm
     unfold F₀ g; rw [Finset.sum_eq_single 0] -- sum reduces
     · simp only [zero_smul,add_zero,Nat.factorial_zero,Nat.cast_one,pow_zero,div_one,one_smul,t,dz,Function.iterate_zero,id_eq,Nat.sub_zero]
     · intro i hi he; simp [zero_pow he]
     · simp
end YM.Comparison.RG02.Assembly.Clipper
