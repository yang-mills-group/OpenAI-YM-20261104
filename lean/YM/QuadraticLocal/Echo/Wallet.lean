import YM.QuadraticLocal.Echo.Scone
import YM.QuadraticLocal.Aperture.Endow
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type*} {V:Type}[Fintype V][DecidableEq V]{G:Gauge} {k j e d i:ℕ} {a σ Z τ A:ℝ} {n:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
namespace Trace
variable (q:V)(W:V→Site n)(X: Roll G V)(h:X.Faith (univ:Finset V) q k σ A)(x:Apex n G)
local notation "ζ"=> X.Ty
local notation "E"=> Apex n G
local notation "Λ"=> Kinetic.Port.exteriorL G n
variable (hp:PaintSupply G i Z)(b:ℝ)(hb:0 < b)(hx:0<σ)
variable (he:e≤j) (hi:j-e+k ≤ i)
local notation "Ω"=> Spot.label q W X
local notation "χ" z:max => ‖((b⁻¹:ℝ) • z)‖
abbrev upper (G:Gauge)(a σ b:ℝ)(i k:ℕ)(F:ℝ):=(∑ v∈ Finset.range (k+1), Trace.branch G a σ i v) * (1+F)^i -- b unused
local notation "U"=> upper G Z σ b i k (χ x)
local notation "η"=> castable q W X
local notation "Hs" v:max=> η j e b v
variable (s:Finset X.Ty) (C:ℝ)
include h hp hi he hx hb
def rent (σ:ℝ)(u:X.Ty):= if u∉s ∧ Spot.Entails (X.leg u) q W then X.price σ u else 0
local notation "Y₀"=> rent q W X s
lemma renter (f : X.Ty) : |η j e b f x| ≤ X.price σ f * ((↑(j+1):ℝ)*(1+|b|)^j * U) := by
 let L:= Trace.upper G Z σ b i k (χ x); let v:= X.price σ f; have hn:0 ≤ v:= Lantern.fee_nn ..; have ht:0≤ L:= by
     have ht i':0≤ branch G Z σ i i':= by unfold branch; have h:=Uniform.pathPrice_pos hp (mul_pos two_pos hx); positivity
     unfold L Trace.upper; exact mul_nonneg (Finset.sum_nonneg fun x _=>ht x) (by positivity) -- `simp`
 rw [sum_turn q W X h x hp b hb hx he hi]; refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (s:= Finset.range (j+1)) (f:=fun d=> |b^d * Spot.label q W X e d (bend b x) f|) (g:=fun _=> (1+|b|)^j*(v*L)) ?_).trans_eq ?_); -- initial space before b
 · intro d hD; have hD':d≤j:= Nat.le_of_lt_succ (Finset.mem_range.mp hD); rw [abs_mul,abs_pow]; apply mul_le_mul ((pow_le_pow_left₀ (abs_nonneg _) (le_add_of_nonneg_left zero_le_one) d).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) hD')) _ (abs_nonneg _) (by positivity); exact (lumen q W X h x hp b hb hx hi d hD' f).trans_eq (mul_assoc ..)
 rw [Finset.sum_const, nsmul_eq_mul,Finset.card_range]; change (↑(j+1):ℝ) * _ = v*( _ *L); ring
set_option quotPrecheck false
local notation "Wb" => ((↑(j+1):ℝ)*(1+|b|)^j*upper G Z σ b i k (χ x))
lemma financing (hC:SumBudget (rent q W X s σ) C) : |(∑' i, castable q W X j e b i x) - ∑ i∈s,castable q W X j e b i x| ≤ C * Wb := by
 let f i:=η j e b i x; have hK : Summable f:= by unfold f; simp_rw [sum_turn q W X h x hp b hb hx he hi]; exact summable_sum (fun k hk=>cali q W X h x hp b hb hx he hi k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) -- check name
 let τ:= Wb; let ψ i:= rent q W X s σ i*τ; have hL i':0≤ branch G Z σ i i':=by unfold branch; have h:=Uniform.pathPrice_pos hp (mul_pos two_pos hx); positivity
 have hT:0≤τ:= by unfold τ Trace.upper; exact mul_nonneg (by positivity) (mul_nonneg (Finset.sum_nonneg fun i _=>hL i) (by positivity))
 have he i: ‖(s:Set X.Ty)ᶜ.indicator f i‖ ≤ ψ i:= by
     by_cases ht:i∉s
     · rw [Set.indicator_of_mem (show i∈ (s:Set X.Ty)ᶜ from ht)]; unfold ψ rent; split; exact renter q W X h x hp b hb hx he hi i; next hp=> have hp₁ : ¬ Spot.Entails (X.leg i) q W:= fun he=>hp ⟨ht,he⟩; unfold f castable; rw [if_neg hp₁]; simp
     rw [Set.indicator_of_notMem (show i∉ (s:Set X.Ty)ᶜ from ht),norm_zero]; exact mul_nonneg (hC.1 i) hT -- `ht` of ¬ i∉ s
 have hh: (∑' i,f i)-(∑ i∈s,f i)=∑' i,(s:Set X.Ty)ᶜ.indicator f i:= by rw [← _root_.tsum_subtype,← Finset.sum_coe_sort, ← hK.tsum_subtype_add_tsum_subtype_compl (s:Set X.Ty), ← tsum_fintype (L:=.unconditional _)]; exact add_sub_cancel_left _ _
 let ht:Summable ψ:=hC.2.1.mul_right τ; have hx':= (hK.indicator (s:Set X.Ty)ᶜ).norm
 change |(∑' i,f i)-(∑ i∈s,f i)| ≤ _; rw [hh]; refine (norm_tsum_le_tsum_norm hx').trans ((hx'.tsum_le_tsum he ht).trans ?_); unfold ψ; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hC.2.2 hT
end Trace
end YM.QuadraticLocal.Echo
