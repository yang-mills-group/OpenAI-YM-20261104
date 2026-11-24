import YM.Comparison.RG02.Moving.Path
/-!
# Push-forward of Wick polynomials, BEFORE transporting positive-grade norm statements

Finite polynomial board through r. The second-order half logarithm charged, the constitutive
ranks & valuation remain. For the local no-hole cumulants, both the analytic discrepancy
and the marker radius costs elsewhere; here identify the target JET. One-field period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree YM.Next.Rank
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I J : Type} {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [DecidableEq I]
variable [FiniteDimensional ℝ X] [Fintype V]

namespace Cargo
variable (x:X) (l:Hot R→ℕ) (F:Hot R→House X I→ℂ) (f:House X I→ℝ)
    (r : ℕ)
local notation "E" => House X I
local notation "Ω"=>Assembly.generator ((1,x,0):E) (reach X) l F f r
local notation "Pt"=> Normal.poly I
variable (s:R.Mode)
def olds (k : ℕ) := (k.factorial:ℂ)⁻¹ • Cloud.integrand Ω (Join.pair s (pick r k))
local notation "♯"=> Assembly.prescription ((1,x,0):E) (reach X) l F f

variable {k : ℕ}
lemma olds_read (v:I→ℝ) (he : k≤r) : Cloud.paint v (olds x l F f r s k)=Assembly.rows (Assembly.expansions l F f) s k (season x v):= by
    rw [olds,_root_.map_smul,Cloud.before_log,Assembly.colors, ← Assembly.exponent_identity,polarization,picked _ he,smul_eq_mul,inv_mul_cancel_left₀ (by exact_mod_cast (Nat.factorial_pos k).ne' : (k.factorial:ℂ)≠0)]
    rfl
omit [FiniteDimensional ℝ X] in
lemma owed_gaussian (Q : Matrix I I ℝ) (h : Q.IsSymm) (he : k≤r) : Cloud.wick Q h 0 (olds x l F f r s k)=detail (♯ Q h r) s k := by
   unfold detail observe; rw [if_pos he, Poly.part_smul,olds,_root_.map_smul]; rfl

def path (x:X) (t:ℝ) := (t,t • x)
omit [FiniteDimensional ℝ X] in
@[fun_prop] lemma smooth_path : ContDiff ℝ ω (path x) := by unfold path; fun_prop
omit [FiniteDimensional ℝ X] in
lemma path0 : path x 0=0:= Prod.ext rfl (zero_smul ℝ x)
omit [FiniteDimensional ℝ X] in
lemma path_home : Tendsto (path x) (𝓝 0) (𝓝 0) := (path0 x) ▸ (smooth_path x).continuous.tendsto 0 -- which direction?

variable (C:Field X I)
def manifesto (t:ℝ) := ∑ k∈range (r+1),(t:ℂ)^k • C.sheet (path x t) (olds x l F f r s k)
local notation "ψ"=> manifesto x l F f r s C
lemma sheet_flow (q : ℕ→ Pt) : Fibre (fun t:ℝ=> ∑ k∈range (r+1), (t:ℂ)^k • C.sheet (path x t) (q k)) := by
   refine Fibre.sum (Finset.range (r+1)) (fun k (t:ℝ)=> (t:ℂ)^k • C.sheet (path x t) (q k)) (fun i _=> ?_)
   let p : Regulator X→Pt := fun z=> C.sheet z (q i)
   have he : Fibre p:= C.sheet_live _
   change Fibre (fun t:ℝ=>(t:ℂ)^i • (p ∘ path x) t)
   exact Fibre.scale (he.maps (path0 x) (smooth_path x).contDiffAt) (fun t:ℝ=> (t:ℂ)^i) (Complex.ofRealCLM.contDiff.contDiffAt.pow i)

lemma manifesto_smooth : Fibre ψ := sheet_flow x r C (olds x l F f r s)
lemma manifesto_read (t:ℝ) (v:I→ℝ) : Cloud.paint v (ψ t)=Zone.eval (Assembly.rows (Assembly.expansions l F f) s) r t (season x (C.link x t *ᵥ v)):= by
   unfold manifesto; rw [_root_.map_sum]; apply Finset.sum_congr rfl; intro i hi
   rw [_root_.map_smul, C.sheet_reads, olds_read x l F f r s _ (mem_range_succ_iff.mp hi), smul_eq_mul]
   symm; rw [Complex.real_smul,Complex.ofReal_pow]; rfl

def cost (t:ℝ) := Assembly.prescription (1,x,0) (reach X) l F f (C.Q (path x t)) (C.symmetric (path x t)) r
lemma shift_gaussian (t : ℝ) (he : (C.link x t).transpose*C.gram (path x t)*(C.link x t)=C.gram 0) (hv : 0<(C.link x t).det) : Cloud.wick (C.Q 0) (C.symmetric 0) 0 (ψ t)=(value (t:ℂ) (cost x l F f r C t)).part s:= by
   unfold manifesto; rw [_root_.map_sum,vpart]; apply sum_congr rfl; intro i hi
   rw [_root_.map_smul, ← C.uses_wick (s:=path x t) he hv, owed_gaussian x l F f r s _ _ (mem_range_succ_iff.mp hi)]; rfl
end Cargo
end YM.Comparison.RG02.Moving
