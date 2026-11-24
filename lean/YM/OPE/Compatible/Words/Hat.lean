import YM.OPE.Compatible.Words.Rale
/-!
# Exponential reading at all ranks
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {I J:Type}[Fintype I]{n k m d:ℕ}
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
variable (Z:E→L[ℝ] PAD I)(x:PAD I) (t:ℝ)
local notation "P!"=> PAD I
lemma deriveE {D:End ℝ (Song P!)}(hp:reduces (harmon P!) D)(p:Song P!)(n:ℕ)(h:p∈harmon P! n): HasDerivAt (fun t:ℝ=> Strike n (fixExp D t n p) x) (Strike (n-1) (fixExp D t (n-1) (D p)) x) t:=by
     let W(k:ℕ):=(D^k) p; let U(i:ℕ)(t:ℝ):= t^i/(i.factorial:ℝ)*Strike n (W i) x; let f(k:ℕ):= t^k/(k.factorial:ℝ)* Strike (n-1) (W (k+1)) x
     have hv: (fun t=>Strike n (fixExp D t n p) x)=(fun t=> ∑ i∈range (n+1), U i t):=by funext t; change callP n x _=_;rw [Hflow,map_sum]; exact sum_congr rfl fun i _=> map_smul ..
     rw [hv]; have he(k:ℕ): ((D^k) (D p))=W (k+1):=by unfold W; rw [pow_succ,End.mul_apply]
     rw [show Strike (n-1) (fixExp D t (n-1) (D p)) x = ∑ i∈range (n-1+1),f i from ?_, funext (show ∀ t, ∑ i∈range (n+1),U i t=(∑ i∈range n,U (i+1) t)+U 0 t from fun i=>sum_range_succ' ..)]; swap
     · change callP (n-1) x _= _; rw [Hflow,map_sum]; apply sum_congr rfl; intro i _; rw [map_smul,he]; rfl
     let T(i:ℕ)(k:ℝ):= k^i; have hz : HasDerivAt (U 0) 0 t:=by rw [show U 0=(fun k=> Strike n p x) by ext1; simp [U,W]]; exact hasDerivAt_const ..
     have hh(i:ℕ)(hi:i∈range n): HasDerivAt (U (i+1)) (f i) t:=by
          have hl: (T (i+1))=fun t:ℝ=> t^(i+1):=rfl
          convert! ((((hasDerivAt_id' t).pow (i+1)).div_const (((i+1).factorial):ℝ)).mul_const (Strike n (W (i+1)) x)) using 1; simp only [Nat.add_sub_cancel,mul_one]; have ht:= (iterateD hp h (i+1)).1
          rw [← starP _ ht (by omega) x]; unfold f; rw [← starP _ ht (by omega) x]; rw [Nat.factorial_succ]; push_cast; field_simp -- maybe cast
     have hc:= (HasDerivAt.fun_sum (u:=range n) (A:=fun i=> U (i+1)) hh).add hz; rw [add_zero] at hc; convert! hc using 1; by_cases ht:n=0
     · subst n; rw [Nat.zero_sub,sum_range_one,sum_range_zero]; unfold f; rw [show W (0+1)=0 from (iterateD hp h 1).2 (by decide),show Strike _ _ _=0 from (show Strike (0-1) (0:Song P!) x=0 from by simp [Strike,Tensor.diagonal]),mul_zero]
     rw [Nat.sub_add_cancel (by omega)]
lemma basisH (p:Song P!)(h:p∈harmon P! n):
    A.average μ (fun y=> Strike n p (x+t • Z y))= Strike n (fixExp (opus (chamber A Z)) (t^2/2) n p) x:=by
         let D:= opus (chamber A Z); have hv:reduces (harmon P!) D:=by simpa only [one_smul] using opusReducer (chamber A Z) 1
         let z(t:ℝ):= t^2/2
         have hp(k:ℕ)(p:Song P!):
             Strike k (fixExp D (z 0) k p) x= A.average μ (fun y=> Strike k p (x+(0:ℝ) • Z y)):=by
              rw [show fixExp D (z 0) k=1 from ?_]; simp_rw [zero_smul,add_zero,singleConst]; rfl -- rotate
              unfold fixExp;rw [show z 0=0 from by unfold z;norm_num,sum_eq_single 0];simp; exact fun i _ hi=>by simp [hi]
              simp
         induction n using Nat.strong_induction_on generalizing t p with
         | h n ih=>
            let Y(t:ℝ):= Strike n (fixExp D (z t) n p) x; let W(t:ℝ):= A.average μ (fun y=> Strike n p (x+t • Z y)); let U(t:ℝ):= t*A.average μ (fun y=>Strike (n-1) (D p) (x+t • Z y))
            have hx(t:ℝ):HasDerivAt W (U t) t:=pet μ A Z x t p h; have ht(t:ℝ): HasDerivAt Y (U t) t:=by
                 have he:HasDerivAt z t t:=by convert! (((hasDerivAt_id' t).pow 2).div_const 2) using 1; simp
                 convert! ((deriveE x (z t) hv p n h).comp t he) using 1; unfold U; rw [mul_comm]; by_cases ht:n=0
                 · simp_rw [show D p=0 from (hv n p h).1 ht,map_zero]; simp only [Strike,Tensor.diagonal,Pi.zero_apply,_root_.zero_apply,sum_const_zero, singleConst]
                 congr 1; exact ih (n-1) (by omega) t _ ((hv _ _ h).2)
            have hz:Y=W:= eq_of_fderiv_eq (𝕜:=ℝ) (fun i=>(ht i).differentiableAt) (fun i=>(hx i).differentiableAt) (fun i=> (ht i).hasFDerivAt.fderiv.trans ((hx i).hasFDerivAt.fderiv).symm) 0 (hp n p)
            exact congr_fun hz.symm t
end YM.OPE.Silt
