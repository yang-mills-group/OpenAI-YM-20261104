import YM.X.Haze.Ear
import YM.X.Grow.Output
/-!
# component fees at tower monomials and low/high multiplication
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
variable {I V:Type*}(w:V→ℕ)
def sauce (a:ℝ): Module.End ℝ (Long G) := LinearMap.pi fun i:ℕ=> a^(i+1) • LinearMap.proj i
lemma power_sauce (a:ℝ)(x:Long G)(n:ℕ): sauce a x n=a^(n+1) • x n:= rfl
lemma pepper (x:Long G)(a:ℝ)(p:Book G) : probeL (sauce a x) p=probeL x (Perch.jets (vapor G) a p):= by
   apply DFunLike.congr_fun (g:=(probeL x).comp (Perch.jets (vapor G) a)); ext1 i; rw [AlgHom.comp_apply,Perch.jets,aeval_X,map_mul]; change probeL _ _=(probeL x) ((C ((a:ℂ)^vapor G i)))*_; simp only [probeL,aeval_X,aeval_C,power_sauce,map_smul,MvPolynomial.algebraMap_eq,smul_eq_mul]; push_cast; rfl -- rhs cast mul
abbrev leaf (w:V→ℕ)(i:ℕ) (p:poly V):= weightedHomogeneousComponent w i p
lemma heel (p:poly V)(a:ℂ)(h:IsWeightedHomogeneous w p n):Perch.jets w a p=a^n • p:= by ext i; rw [Perch.jets_coeff,coeff_smul,smul_eq_mul]; by_cases hx:i ∈ p.support; rw [h (mem_support_iff.mp hx)]; rw [MvPolynomial.notMem_support_iff.mp hx,mul_zero,mul_zero]
lemma dinner (p:Book G)(i:ℕ)(x: Long G)(a:ℝ): probeL (sauce a x) (leaf (vapor G) i p) = a^i • probeL x (leaf (vapor G) i p):= by rw [pepper,heel _ _ _ (weightedHomogeneousComponent_mem ..), map_smul, ← Complex.ofReal_pow]; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) ..).symm --] -- args
lemma mix (p s: poly V) (d:ℕ) : level w d (p*s) = level w d (level w d p * level w d s):= by
    change Rise.trim _ _ _ = Rise.trim (Rise.trim _ _ _*Rise.trim _ _ _) _ _; rw [fine_weight, mul_comm p (Rise.trim _ _ _),fine_weight, mul_comm p s]
lemma leaf_level (p:poly V)(i:ℕ)(he:i≤d):leaf w i (level w d p)=leaf w i p := by ext x; simp only [leaf,coeff_weightedHomogeneousComponent]; change (if Finsupp.weight w x=i then coeff x (Rise.trim _ _ _) else _) =_; rw [Rise.trim_coeff]; split_ifs <;> first|rfl|omega -- implicit i
lemma chop (p s:poly V)(i j:ℕ) : IsWeightedHomogeneous w (leaf w i p*leaf w j s) (i+j):= IsWeightedHomogeneous.mul (weightedHomogeneousComponent_mem ..) (weightedHomogeneousComponent_mem ..)
lemma leaf_mul (p s:poly V)(he:k≤d) : leaf w k (p*s)= ∑ i∈range (d+1),∑ j∈range (d+1), if i+j=k then leaf w i p*leaf w j s else 0:= by
    rw [← leaf_level _ _ _ he,mix,leaf_level _ _ _ he,trimmer,trimmer]; unfold leaf; simp_rw [Finset.sum_mul, Finset.mul_sum,map_sum]; refine sum_congr rfl (fun i _=> sum_congr rfl fun j _=>?_); split; next hx=> exact (hx ▸ (show IsWeightedHomogeneous w (leaf w i p*leaf w j s) (i+j) from chop ..)).weightedHomogeneousComponent_same
    next hx=> exact (chop w p s i j).weightedHomogeneousComponent_ne _ (Ne.symm hx)
lemma level_high (p s:poly V)(d:ℕ) : level w d p*level w d s-level w d (p*s)= ∑ i∈range (d+1),∑ j∈range (d+1), if d < i + j then leaf w i p*leaf w j s else 0:= by
    rw [mix w p s, trimmer (p:=p), trimmer (p:=s)]; simp_rw [Finset.sum_mul,Finset.mul_sum, map_sum,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl fun j _=>?_); split
    next h=>rw [(Strong.of_pure (chop w p s i j)).none h,sub_zero]
    next h=> rw [trimmer_hom (not_lt.mp h) (chop w p s i j),sub_self]
end YM.PositionX.Clove
