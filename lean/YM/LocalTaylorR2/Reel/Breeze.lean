import YM.LocalTaylorR2.Reel.Trust
import YM.LocalTaylorR2.Reset.Docket
import Mathlib.Analysis.PSeries
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
/-!
 # SDB (support estimates) and simple physical accumulation for the *entire finite history*
 Local estimates at order l retained along step estimates. Every finite regulator N, all steps
 from the chosen m. Cost after extracting β by true-scale inverse threshold. This does not replace
 the incoming β in the predictors, which still use the exact (N,n) trajectory's parameters.
 -/
variable {G:Gauge} (g:G.Simple) (A:Levels G)
local notation "x"=> A.clock.hatBeta
local notation "Δ"=> A.budget
variable {m n:ℕ}
include g
open Recoil
-- extra powers ℓ=6 above target to pay β inverse and to sum a p-series; plus any requested remaining K.
def margin (p K:ℕ):= p+2*K+6
def march_s (G:Gauge):=G.slopeConstant * Real.log 3
def living (G:Gauge):=min 1 (march_s G)
lemma fertile : 0<living G:=lt_min zero_lt_one (mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos (by norm_num)))
lemma stance (i:ℕ): x i + march_s G ≤ x (i+1):=by
   rw [← Next.Scheduling.Deployment.hat]; -- search
   apply add_le_add_right; apply mul_le_mul_of_nonneg_left _ (Gauge.slopeConstant_pos g).le
   exact Real.log_le_log (by norm_num) (by exact_mod_cast (A.S.block_large i))
lemma taller : Monotone (x):= monotone_nat_of_le_succ fun i=> le_trans (le_add_of_nonneg_right (show 0 ≤ march_s G from (fertile g|>.le).trans (min_le_right ..))) (stance g A i)
lemma funded (i:ℕ): living G*((i:ℝ)+1) ≤ x i:=by
   induction i with
   | zero=> simpa [living] using (le_trans (min_le_left 1 (march_s G)) (A.fits.delayed 0).le)
   | succ i ih=> apply le_trans _ (stance g A i); push_cast; rw [mul_add]; exact add_le_add ih (by rw [mul_one]; exact min_le_right ..)
omit g
lemma aspire (i:ℕ):0<x i:=zero_lt_one.trans (A.fits.delayed _)
lemma appeal (p K:ℕ)(ε:ℝ) (k:ℕ): (x k)^K*(x k * upfront (x k) (margin p K) ε)=(x k)^requested (p+1) ε * (2 / (x k)^ (2:ℕ)):=by
   let y:=x k; have hr:= aspire A k; unfold upfront
   have he : requested (margin p K +1) ε+(K:ℝ)+1+2=requested (p+1) ε:=by unfold margin requested; push_cast; ring
   let v:=requested (margin p K+1) ε; have hv: (x k)^ v*(x k)^K*x k*(x k)^2=(x k)^requested (p+1) ε:= by
      simp_rw [← Real.rpow_natCast]; -- adding 1 & ^2.. ensure coercion
      rw [← Real.rpow_add hr, show x k ^(v+(K:ℝ))*x k=x k^(v+(K:ℝ))* x k^(1:ℝ) from by rw [Real.rpow_one],← Real.rpow_add hr, ← Real.rpow_add hr, ← he]; norm_num; rfl
   rw [← hv]; unfold v; field_simp
include g
lemma base_income (p:ℕ)(he:m ≤ n){ε:ℝ}(hv:ε≤1): x n^requested (p+1) ε ≤ x m^requested (p+1) ε := Real.rpow_le_rpow_of_nonpos (aspire A _) (taller g A he) (by unfold requested; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p])

def sizeFar (G:Gauge) i:= 1/(living G)^ (2:ℕ) * (1/|((i:ℕ):ℝ)+1| ^ (2:ℝ))
def zig (G:Gauge) := 6*∑' i:ℕ,sizeFar G i
lemma rises (i:ℕ): 1/(x i)^ (2:ℕ) ≤ sizeFar G i:=by
    let v:= ((i:ℕ):ℝ)+1; have hv:0<v:=by unfold v; positivity
    unfold sizeFar; change _ ≤ _*(1/|v| ^ (2:ℝ)); rw [abs_of_nonneg hv.le,Real.rpow_two]; have hp:= fertile g; rw [show 1/(living G)^ (2:ℕ)*(1/v^ (2:ℕ))=1/(living G*v)^ (2:ℕ) by field_simp]; gcongr; exact funded g A i
lemma calibrate (S:Finset ℕ)(hm:∀ i∈S,m ≤ i)(p K:ℕ){ε:ℝ}(ht:ε≤1)(s b:ℕ→ℝ)
    (hs:∀ i∈S, s i ≤ upfront (x i) (margin p K) ε)(hb:∀ i∈S, (Δ i).threshold^2*b i ≤ upfront (x i) (margin p K) ε):
     ∑ i∈ S,x i^K * (s i+b i+upfront (x i) (margin p K) ε) ≤ zig G * x m^requested (p+1) ε := by
  have hY := ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).mul_left (1/(living G)^ (2:ℕ)); let W i:= upfront (x i) (margin p K) ε
  have he : ∀ i,0≤ sizeFar G i:=by intro i; unfold sizeFar; positivity
  let c:= x m^requested (p+1) ε; have hc:0≤c:= Real.rpow_nonneg (aspire A _|>.le) _; change (∑ i∈S,x i^K*(s i+b i+W i))≤ zig G*c
  calc
   _ ≤ ∑ i∈S,6* sizeFar G i*c := by
      apply sum_le_sum; intro i hi
      let y:= x i; let q:= (Δ i).threshold; have hx:1≤y:=(A.fits.delayed _).le; have hg:0 ≤ W i:= by have he':0<y:=aspire A i; exact mul_nonneg zero_le_two (Real.rpow_nonneg he'.le _); -- braces
      have hq:0<q := (Δ i).threshold_pos; have hk:q⁻¹ ^2 ≤ y:= le_trans (b:=(Real.sqrt y)^2) (pow_le_pow_left₀ (inv_nonneg.mpr hq.le) (Recoil.inv_bound A i) 2) (by rw [Real.sq_sqrt (zero_le_one.trans hx)])
      have hy:0≤ y^K:= pow_nonneg (zero_le_one.trans hx) _
      have hC₁: ∀ X:ℝ,q^2*X≤ W i→ X ≤ y* W i:=by
          intro X hv; 
          calc X ≤ W i/(q^2) := (le_div_iff₀ (by positivity)).2 ((mul_comm _ _).trans_le hv)
               _ = (q⁻¹^2)*W i:= by field_simp
               _ ≤ _:= by gcongr
      calc
       _ ≤ y^K*(3*(y*W i)):= by
          apply mul_le_mul_of_nonneg_left _ hy; linarith only [hC₁ _ (hb i hi),show s i≤ W i from hs i hi, show W i≤ y* W i from le_mul_of_one_le_left hg hx]
       _ = 3*(x i^requested (p+1) ε)*(2*(1/(x i)^ (2:ℕ))):=by rw [mul_left_comm, show y^K*(y* W i)= _ from appeal A p K ε i]; ring
       _ ≤ _:= by
         have he0:0≤1/(x i)^ (2:ℕ):=by positivity
         calc _ ≤ 3*c*(2*(sizeFar G i)):= mul_le_mul (mul_le_mul_of_nonneg_left (base_income g A p (hm _ hi) ht) (by norm_num)) (mul_le_mul_of_nonneg_left (rises g A i) zero_le_two) (mul_nonneg zero_le_two he0) (mul_nonneg (by norm_num) hc)
              _ =_:= by ring
   _ = (6*∑ i∈ S,sizeFar G i)*c:=by rw [← Finset.sum_mul,Finset.mul_sum]
   _ ≤ _:= by unfold zig; gcongr; exact Summable.sum_le_tsum S (fun i hi=>he i) hY -- lemma spelling
end YM.LocalTaylorR2.Reel
