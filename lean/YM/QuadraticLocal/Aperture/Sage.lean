import YM.QuadraticLocal.Aperture.Lyre
import YM.QuadraticLocal.Sunrise.Harvest
import YM.Comparison.Cumulants.Factorial
import YM.RG.Bounded
/-!
 # The polynomial of real-mark values on the weighted Regulated slice. No ghosts
 ID supports expected AFTER shifting (log numerator involving real, still needs regular contribution
 & K readdress). Here only drawn on the EXACT normalized slice weights and moments. Use Point
 stamp variants when supplying masks. Keeps absolute-scale ledger of Step.Member.A.Q.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Marker Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
variable {X Z V:Type} [Fintype V][DecidableEq V]
namespace Sage
variable [MeasurableSpace X] (W:X→ℝ) (μ:Measure X) [IsFiniteMeasure μ] (ρ:V→X→ℝ)
variable (hW:RG.Envelope W) (hM:0≤W) (hZ: 0<∫ i, W i ∂μ) (hρ:∀ i,RG.Envelope (ρ i))
local notation "𝕊"=> univ
local notation "V₁"=> Knife V
abbrev moment (x:X→ℝ):= (∫ i,W i*x i ∂μ)/(∫ i,W i ∂μ)
local notation "Z"=> moment W μ
local notation "P"=> (Knife V × X)
include hW
lemma price_sum {a b:X→ℝ}(ha:RG.Envelope a)(hb:RG.Envelope b): Z (a+b) =Z a + Z b:= by
 unfold moment; erw [← add_div]; congr 1; simp_rw [Pi.add_apply,mul_add]; exact MeasureTheory.integral_add (Envelope.integrable (hW.mul ha) μ) (Envelope.integrable (hW.mul hb) μ)
omit hW
lemma price_scale (a:X→ℝ)(b:ℝ): Z (b•a)= b*(Z a):=by
 unfold moment; simp_rw [Pi.smul_apply,smul_eq_mul, mul_left_comm (W _) b, integral_const_mul,← mul_div_assoc]
include hM hW hZ
lemma banking (a:X→ℝ)(f:ℝ)(hx:∀ i:X, W i≠0→ ‖a i‖≤ f) : |Z a|≤ f:=by
 by_cases he:∃ i,W i≠0; swap; · push Not at he; simp_rw [he] at hZ; simp at hZ
 obtain ⟨z,hz⟩:=he; have hf:0 ≤ f:=(norm_nonneg (a z)).trans (hx z hz)
 unfold moment; rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]; by_cases ht : Integrable (fun i=>W i*a i) μ; swap; · rw [integral_undef ht,abs_zero]; exact mul_nonneg hf hZ.le
 rw [mul_comm f, ← integral_mul_const]; apply (norm_integral_le_integral_norm (μ:=μ) (f:=fun i=> W i*a i)).trans (integral_mono ht.norm ((hW.integrable μ).mul_const _) (fun i=>?_)) -- Real
 rw [norm_mul,Real.norm_of_nonneg (hM i)]; by_cases hx': W i=0; rw [hx',zero_mul,zero_mul]; exact mul_le_mul_of_nonneg_left (hx i hx') (hM i)
omit hM hW
lemma price_one : Z (fun (_:X)=> (1:ℝ))=1:=by unfold moment; simp_rw [mul_one,div_self hZ.ne']
omit hZ
abbrev entry_d (X:Type)[MeasurableSpace X]: Aperture.Drawer X:=⟨Envelope,Envelope.const,Envelope.add,Envelope.mul⟩ -- implicit V,X
abbrev shadow (Y:Type): Aperture.Drawer Y:= ⟨fun _=>True,fun _=>trivial,fun _ _=>trivial,fun _ _=>trivial⟩
variable {k n:ℕ}
local notation "Region"=> entry_d X
abbrev member (p:Drawer.Knife V × X):ℝ:=∑ i:V,p.1 i * ρ i p.2
abbrev ratioN (k:ℕ)(V' : V₁):ℝ:=moment W μ (fun x=> ((k.factorial:ℝ)⁻¹) * Sage.member ρ (V',x)^k)
abbrev desk_mark (k:ℕ): Knife V × X→ℝ:= (k.factorial:ℝ)⁻¹ • (member ρ)^k
local notation "φ"=> ratioN W μ ρ
local notation "ℱ"=> member ρ
include hρ
lemma school_point : Drawer.School Region 1 (ℱ):= by
 let f(i:V)(p:P):= p.1 i*ρ i p.2; rw [show member ρ = _ from (show member ρ=∑ i:V,f i from funext fun p=> (Finset.sum_apply p univ f).symm)]; exact School.pivot f fun i _=> School.sit_v _ _ i (ρ i) _ (hρ i) zero_lt_one
lemma school_spell (j:ℕ) : Drawer.School Region j ((ℱ)^j):= by induction j with | zero=> rw [pow_zero]; exact School.stable _ _ _ _ | succ j ih=> rw [pow_succ]; exact ih.product (school_point ρ hρ)
lemma school_ratio : Drawer.Inn V (entry_d X) 1 (desk_mark ρ):=fun i=> (Nat.div_one i).symm ▸ (School.scale (school_spell ρ hρ i) _)
include hW
lemma budget_ratio (X':Type): Inn V (shadow X') 1 (fun i (x:(V→ℝ) × X')=> φ i x.1):= Inn.take_valley (school_ratio ρ hρ) (fun (_:X') f=> moment W μ f) (shadow X') (fun _ _=>trivial) (fun u v hu hv _=> Sage.price_sum W μ hW hu hv) (fun u _ c _=> price_scale W μ u c) -- defs
lemma clearR : Clear (ratioN W μ ρ):= by intro i; exact School.understands (budget_ratio W μ ρ hW hρ ℝ i) (0:ℝ)
omit hW hρ
include hZ
lemma present : (φ) 0=1:= by ext1 z; unfold ratioN; simp_rw [Nat.factorial_zero,pow_zero,Nat.cast_one,inv_one,mul_one]; exact price_one W μ hZ
include hρ hW
local notation "ℓ"=> Inn V (shadow ℝ)
lemma crystal : ℓ 1 (fun i (x:(V→ℝ) × ℝ)=> (LOG (ratioN W μ ρ) i x.1)):= by
 let v i (x:(V→ℝ) × ℝ):= (φ i) x.1; have he:v 0=1:=by ext1 z; exact congr_fun (present W μ ρ hZ) z.1
 exact Inn.loose (budget_ratio W μ ρ hW hρ ℝ) he
end Sage
end YM.QuadraticLocal.Aperture
