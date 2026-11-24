import YM.RG01Estimate.Normalize
import YM.RG01Estimate.Stellar
/-!
# Scalar/relative true conditional logarithm on the small torus.

Doesn't compare basis-dependent scalar reset estimates. No marked polynomial
log at K where denominator might vanish. Pure sector point comparisons on an
auxiliary shape, often the hypotheses can be paid without knowing anything
about all-field denominators on the main torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Series
variable {G : Gauge}
section C
variable {c f L:Side}{S:StepData c f}(F:Forest S.ratio)(T:Tube G S)(B:BudgetPoint)(k:S.Choices)
   (ρ:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "q" => Lapis.orbit F ρ
local notation "J" => sweep (M 0)⁻¹
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
     {e:Config G f→ E}(H:Poll.Body (Precision.Key F G) → ℝ × Positions (Uniform.Primary c G) → E)
     (β:ℝ)
local notation "g" => gStep β
local notation "V" => (fun y : X=> represent (tint G _ y))

def vintage (r:ℕ)(y:X) := Laplace.step (fill F T ρ k O H) Set.univ J r y

lemma dignified {j n l:ℕ}{G':ℝ}{x:X}(hx : Brush n (gStep β^j*G') 1 (organic F T ρ k O β e-purses F T ρ k O H β j) x)
    (hb : ∀ M'< j, Brush (l-M') G' 1 (Laplace.step (fill F T ρ k O H) Set.univ (Poll.sweep (M 0)⁻¹) M') x) (hr:n+j≤ l)(hβ:0<β):
    Hon g j n (vintage F T k ρ O H) (organic F T ρ k O β e) G' x:= by
    have hk:= Fare.gS β hβ; have hz : 0 ≤ G':= nonneg_of_mul_nonneg_right hx.nonneg (pow_pos hk.1 j) -- order
    refine ⟨hz,fun i hi=> (hb i hi).smaller (by omega),?_⟩; rw [abs_of_pos hk.1]; exact hx

variable (v : Poll.Body (Precision.Key F G) → ℝ× Positions (Uniform.Primary c G)→ℝ)(Z:Config G f →ℝ)
local notation "π'" => (vintage F T k ρ O v)
-- assumes analytic order-vacuum zero, not denominator identification
lemma still_unit (z:X) (he: ∀ i:Y,v i (0,z)=1) :
     vintage F T k ρ O v 0 z = 1 := by
   have h (i:Y): voteForm (Lapis.table F k T.up T.high) (mist F O T.up) (Lapis.orbit F ρ) M i (0,z)=1:= by simp only [voteForm,rho,zero_smul]; rw [Lantern.zeroC,Real.exp_zero]
   change ∫ i in Set.univ,voteForm _ _ _ M i (0,z) • v i (0,z) ∂J=1; simp_rw [h,he,one_smul,setIntegral_univ,integral_const,probReal_univ,one_smul]

def report (r:ℕ) (x:X):= Stellar.model F T k ρ O r β x+ Series.trunc (Series.logarithm (vintage F T k ρ O v) r) g r x
-- includes true actual scalar

def vacuumS (x:X):= Real.log (Conditioning.den S β Z (g • x))
lemma near_v {x:X}(h: ContinuousAt (organic F T ρ k O β Z) x) (hn : 0< organic F T ρ k O β Z x)(hO:LocalRatio O)(hp:0<β) :
    vacuumS (S:=S) β Z =ᶠ[𝓝 x] fun x' => Stellar.logprice F T k ρ O β x'+Real.log (organic F T ρ k O β Z x'):= by
  filter_upwards [h.eventually (lt_mem_nhds hn)] with y hy
  have ht : 0 < organic F T ρ k O β Z y:= hy
  let u:= price F T O k ρ β (g • y); have hf:0<u:=price_pos F T O k ρ β hO hp
  have he: Conditioning.den S β Z (g • y)= u*organic F T ρ k O β Z y:= Eq.symm (mul_inv_cancel_left₀ hf.ne' _)
  unfold vacuumS; rw [he,Real.log_mul hf.ne' ht.ne']; rfl

lemma unscan {t δ:ℝ} {n r : ℕ} (hO:LocalRatio O)(he:0<β)(x:X)
    (hf: Hon g r n (logarithm (vintage F T k ρ O v) r) (Real.log ∘ organic F T ρ k O β Z) t x)
    (hg : 0<organic F T ρ k O β Z x) (hp:ContinuousAt (organic F T ρ k O β Z) x)
    (hv: Brush n (g^r*δ) 1 (fun x=> Stellar.logprice F T k ρ O β x-Stellar.model F T k ρ O r β x) x) :
      Brush n (g^r*(δ+t)) 1 (fun x=>vacuumS (S:=S) β Z x-report F T k ρ O β v r x) x := by
   rw [mul_add]; have h:= hf.priced; rw [abs_of_pos (Fare.gS β he).1] at h
   apply (hv.gathering h).shimmy
   filter_upwards [near_v F T k ρ O β Z hp hg hO he] with y hy
   change vacuumS (S:=S) β Z y- (_+_)=_
   rw [hy]; simp [Function.comp_apply]; abel

variable (e)

def normalized (x:X):= (Conditioning.den S β Z (g • x))⁻¹ • Conditioning.roll S β e (g • x)
-- exact denominator in actual aux vacuum for marked moments. Does not require real exterior continuation.
lemma marked_relative {t t' : ℝ}{x:X}{r n:ℕ}(hO:LocalRatio O)(he:0<β)(hp:g≤1)
    (h : Hon g r n (Series.inverse (vintage F T k ρ O v) r) (fun i => (organic F T ρ k O β Z i)⁻¹) t x)
    (p : Hon g r n (vintage F T k ρ O H) (organic F T ρ k O β e) t' x) :
    Hon g r n (convolve (ContinuousLinearMap.lsmul ℝ ℝ) (Series.inverse (vintage F T k ρ O v) r) (vintage F T k ρ O H)) (normalized (S:=S) e β Z) (addition n r 1 t t') x:= by
   refine (h.twins p _ (show |g|≤1 by rw [abs_of_pos (Fare.gS β he).1]; exact hp) (ContinuousLinearMap.opNorm_lsmul_le ..)).shift ?_ (fun _ _=> EventuallyEq.rfl)
   filter_upwards with i
   let a:= price F T O k ρ β (g • i); let u:= Conditioning.den S β Z (g • i); let w:= Conditioning.roll S β e (g • i)
   have ha:a≠0:=(Courtyard.price_pos F T O k ρ β hO he).ne'
   change u⁻¹ • w = (a⁻¹*u)⁻¹ • a⁻¹ • w
   rw [_root_.mul_inv_rev, inv_inv,smul_smul, mul_assoc, mul_inv_cancel₀ ha,mul_one]
end C
end YM.RG01Estimate.Laplace
