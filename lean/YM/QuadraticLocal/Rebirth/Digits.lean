import YM.QuadraticLocal.Rebirth.Links
import YM.QuadraticLocal.Rebirth.Reprints
/-!
# Reitter the entire unmasked connected kernel through a bend of its chart.
 Finite budgets on concerned sources. Cauchy merging (no differentiated volume exchange!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
open QuadraticLocal.Sunrise Marker Earn
variable {ι V α:Type} [DecidableEq V] {R:Census V} {G:Gauge} {n:Side} {P:Passport n V}
open Comparison.RG02 Comparison.RG02.Adjacent
namespace Sleeve
local notation "A"=> (Stationary.Link G n)
variable (X: Row P R G α) (t:α) (w:V→ℕ)
local notation "u★"=> X.lamp.lag
local notation "xρ"=> X.lamp.r
local notation "τ"=> X.lamp.e
variable (M:ι→Row P R G α)
set_option quotPrecheck false
local notation "X'"=> (Stationary.arm G n 1)
local notation "K"=> (Q.Clock.Art.Texture) -- placeholder
variable (Kp:R.Mode)

local notation "V'"=> (fun i:ι=>Sleeve.coin (M i) t Kp)
-- membership must cover all.Label budgets complete.Edge.St.Frame.Consumer.Stock.*
variable (S:Finset ℤ) (hS:∀ i,(M i).lamp.lag∈ S)
variable {a b:ℝ} {u v:ℕ}
variable (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ)
variable [Fintype V]
set_option quotPrecheck false
local notation "PΩ"=> (fun i:ι=>(M i).paint t)
variable (ha: Air.Staff M (fun i:ι=>(M i).paint t) w a u)
local notation "Z"=> (Mutation.stamp M Q h L j)
variable (T:Finset Age)(B:AllOrder.Floe.Layout G)
local notation "k'"=> (Sleeve.coin)
local notation "Y" => Air.craft M (fun i:ι=>(M i).paint t) w B T
local notation "z'"=> (fun z:ℤ=> Chart.tariff Q h L z)
local notation "pℓ"=> ( 𝓝 (0:ℝ))
open Comparison.RG02.Moving Path Shift
local notation "Ξ"=> (caliber Q h).back L
local notation "W₁"=> Sleeve.currency t w M Kp T B
local notation "V₁"=> Sleeve.treasury t M Kp
local notation "H"=> (Z)

def spindle (S:Finset ℤ)(k:ℕ)(x:Stationary.Link G n):ℂ:=∑ i∈range (k+1),∑ z∈S, ( Chart.tariff Q h L z (k-i):ℂ ) * (Sleeve.treasury t M Kp i z x)
local notation "κ" x:max=> ( realOil ) -- placeholder
local notation "g"=> (( Ξ ).rating)
lemma spinner (s:ℤ): let f:=fun x:ℝ=> (g x)^s; motion ((Complex.ofReal)∘ f)= fun i:ℕ=> ((Chart.tariff Q h L s i):ℂ) := by
   intro f; have he : ContDiffAt ℝ ω f 0:= (Ξ).spin _; funext i; unfold motion; change Assembly.jet (Complex.ofRealCLM ∘ f) i 1=_; rw [←Assembly.jet_apply_left Complex.ofRealCLM f i (he.of_le le_top) (1:ℝ) ]; apply congr_arg Complex.ofRealCLM; rw [ iteratedDeriv_eq_iteratedFDeriv ]; rfl -- cast syntax.
include hS ha T B
local notation "Θ"=> (Adjac.Statement)
variable (x:Stationary.Link G n)
-- aperture.Header.Binding.Frame.Inventory_C`. Takes any ξ->...
lemma chronicle :
      (fun u:ℝ=> Adjacent.ages (Sleeve.currency t w M Kp T B) 0 j u ( ( (caliber Q h).back L ).rating u ) x ) =ᶠ[𝓝 0]
      fun u=> ∑ i∈range (j+1),∑ s∈S, (u:ℂ)^i*(( (( (caliber Q h).back L ).rating u ^ s:ℝ):ℂ) * Sleeve.treasury t M Kp i s x):=by
    filter_upwards [(Ξ).bright] with u hu; simp only [Adjacent.ages,zpow_zero,Complex.ofReal_one,one_mul, Adjacent.cover]; push_cast; refine Finset.sum_congr rfl fun i _=>?_ ; rw [seams t w M Kp S hS ha T B i _, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; have hf:= Sleeve.stretches t w M Kp ha T B ( g u ) hu.ne' z x i; simp_rw [Complex.real_smul, Complex.ofReal_pow] at hf; rw [mul_pow, mul_assoc, hf, Complex.ofReal_zpow] -- `Complex.ofReal_zpow` HS? push_cast simplified
local notation "P₀"=> ( Sleeve.spindle t M Kp Q h L ) -- conflict P binder! choose
variable (k:ℕ)(he:k≤j)
include he
lemma born_message :
     Adjacent.born (Sleeve.currency t w M Kp T B) ((caliber Q h).back L) 0 j k x= Sleeve.spindle t M Kp Q h L S k x:=by
    let f (s:ℤ)(v:ℝ):ℂ:= ↑(g v^s:ℝ); let F (i:ℕ) (s:ℤ) (v:ℝ):ℂ:=(v:ℂ)^i * ( f s v* ( V₁ i s x) ); let c n z:= ( Sleeve.treasury t M Kp n z x); let C i (u:ℝ):=∑ s∈S,F i s u; have hm (s:ℤ):ContDiffAt ℝ ω (f s) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((Ξ).spin _); have hx i s:ContDiffAt ℝ ω ( F i s ) 0:= (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul ((hm s).mul contDiffAt_const); have hc i:ContDiffAt ℝ ω (C i) 0:= ContDiffAt.sum fun k _=> hx i k;
    let R':=( range (j+1) ); unfold Adjacent.born; rw [mgerm (chronicle t w M Kp S hS Q h L j ha T B x)]; rw [msum (range (j+1)) C (fun i _=>hc i)]; unfold spindle
    calc
      _ = ∑ i∈range (k+1), motion (C i) k := by
         symm; apply Finset.sum_subset (range_mono (by omega)); intro i hv hh; unfold C; rw [msum _ _ fun j _=>hx i j]; refine Finset.sum_eq_zero fun s _=>?_ ; unfold F; rw [mono_price (f:=fun t=> f s t* c i s) ((hm s).mul contDiffAt_const), if_neg]; simp only [mem_range] at hh; omega
      _ = _ := by
         apply Finset.sum_congr rfl; intro i hi; unfold C; rw [ msum _ _ (fun j _=>hx i j) ]; apply Finset.sum_congr rfl; intro s _; unfold F; rw [mono_price (f:=fun t=> f s t* c i s) ((hm s).mul contDiffAt_const), if_pos (mem_range_succ_iff.mp hi), show (fun t=>f s t*c i s) = fun t=> c i s* f s t from funext fun r=>mul_comm .., mscale _ (hm s), mul_comm]; exact congr_arg (· * c i s ) (congr_fun (spinner Q h L s) (k-i))
end Sleeve
end YM.QuadraticLocal.Rebirth
