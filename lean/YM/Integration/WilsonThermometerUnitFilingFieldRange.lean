import YM.Integration.WilsonThermometerUnitFilingWhole
import YM.Next.FOUNDATIONS.Primary
import YM.Planned.PRIMARY_INTEGRAL_295.Stain

/-! A full signed one-mark return of any finite toll, measured as a scalar
on the genuine older conditional at the identity. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFieldRange
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open Next.Foundations RG16
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "F" => R.family.labels.level d
local notation "T" => R.family.localSection d

def basisCost (G:Gauge) (d:ℕ):ℝ:=(full_value_bound (G:=G) d).choose
def cost (G:Gauge) (d:ℕ) (θ:ℝ):ℝ:=1+basisCost G d*(max 1 θ⁻¹)^d

theorem sectionRow {n:Side} (x:(F).Coeff) (y:Site n) (U:Config G n):
    ‖(T).places x y U‖ ≤ basisCost G d*(F).coeffSize x:=by
  let e:(F).Index→(F).Coeff:=fun a=>Pi.single a 1
  have sum:x=∑a,x a • e a:=by ext a; simp [e,Pi.single_apply]
  let evaluate:(F).Coeff →ₗ[ℂ] ℂ:= {
    toFun a := (T).places a y U
    map_add' a b:=congr_fun ((T).eval_linear.map_add a b) (expandAt y U)
    map_smul' a b:=congr_fun ((T).eval_linear.map_smul a b) (expandAt y U) }
  have row:(T).places x y U=∑a,x a*(T).places (e a) y U:=by
    change evaluate x=∑a,x a*evaluate (e a)
    calc _=evaluate (∑a,x a • e a):=congrArg evaluate sum
         _=∑a,x a*evaluate (e a):=by simp
  rw [row]
  calc _ ≤ ∑a,‖x a*(T).places (e a) y U‖:=norm_sum_le _ _
       _ ≤ ∑a,basisCost G d*‖x a‖:=by
          refine sum_le_sum fun a _=>?_
          rw [norm_mul,mul_comm (basisCost G d)]
          exact mul_le_mul_of_nonneg_left (((full_value_bound (G:=G) d).choose_spec.2 a).2 n y U) (norm_nonneg _)
       _=basisCost G d*(F).coeffSize x:=by rw [Labels.Frame.coeffSize,Finset.mul_sum]

theorem core (x:(F).Coeff):(F).coeffSize ((F).core x) ≤ (F).coeffSize x:=by
  unfold Labels.Frame.coeffSize
  refine sum_le_sum fun a _=>?_
  by_cases h:a=0
  · subst a;simp [Labels.Frame.core,Function.update]
  · simp [Labels.Frame.core,Function.update,h]

private theorem scaling (t θ:ℝ) (nonneg:0 ≤ θ) (tp:1 ≤ t) (cap:θ ≤ t) (x:(F).Coeff):
    (F).coeffSize ((F).scaled θ x) ≤ t^d*(F).coeffSize x:=by
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum];refine sum_le_sum fun a _=>?_
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg nonneg _)]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ nonneg cap _).trans (pow_le_pow_right₀ tp
    (Planned.PrimaryIntegral295.Film.second_fits F a))) (norm_nonneg _)

theorem point {n:Side} (P:Rep G n) (q:Coefficient F n) (y:Site n) {κ M:ℝ}
    (paid:q.remBound y P κ M) (U:Config G n):
    ‖q.exponentialEntry y T P U‖ ≤ cost G d P.p.threshold*(F).coeffSize q.x+M:=by
  let θ:=P.p.threshold
  let t:=max 1 θ⁻¹
  let v:=(F).scaled θ⁻¹ ((F).core q.x)
  have cpos:0 ≤ basisCost G d:=zero_le_one.trans (full_value_bound (G:=G) d).choose_spec.1
  have tp:0 ≤ t:=zero_le_one.trans (le_max_left _ _)
  have scale:(F).coeffSize v ≤ t^d*(F).coeffSize q.x:=
    (scaling R d t θ⁻¹ (inv_nonneg.mpr P.p.threshold_pos.le) (le_max_left ..) (le_max_right ..) _).trans
      (mul_le_mul_of_nonneg_left (core R d q.x) (pow_nonneg tp _))
  have xunit:‖q.x 0‖ ≤ (F).coeffSize q.x:=single_le_sum (f:=fun a=>‖q.x a‖) (fun a _=>norm_nonneg _) (mem_univ 0)
  have span:0 ≤ (F).coeffSize q.x:=Finset.sum_nonneg fun a _=>norm_nonneg _
  have held : ‖masked θ ((T).footprint y) ((T).places v y) U‖ ≤
      basisCost G d*(t^d*(F).coeffSize q.x):=by
    by_cases good:Healthy θ ((T).footprint y) U
    · rw [masked_eq _ _ _ _ good]
      exact (sectionRow R d v y U).trans (mul_le_mul_of_nonneg_left scale cpos)
    · rw [masked_ne _ _ _ _ good,norm_zero]
      exact mul_nonneg cpos (mul_nonneg (pow_nonneg tp _) span)
  have rest:=ordinary q y P paid U
  unfold Coefficient.exponentialEntry
  calc _ ≤ ‖q.x 0+masked θ ((T).footprint y) ((T).places v y) U‖+‖∑'a,q.maskedTerm P a U‖:=norm_add_le _ _
       _ ≤ (‖q.x 0‖+‖masked θ ((T).footprint y) ((T).places v y) U‖)+M:=add_le_add (norm_add_le _ _) rest
       _ ≤ ((F).coeffSize q.x+basisCost G d*(t^d*(F).coeffSize q.x))+M:=
            add_le_add (add_le_add xunit held) le_rfl
       _=cost G d P.p.threshold*(F).coeffSize q.x+M:=by dsimp only [cost,t,θ];ring

variable (simple:G.Simple) {N per m k b u:ℕ} (way:WayStation R.kit)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (ticket:TicketP R.alloy R.kit D Q) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
  (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (top:b ≤ N) (floor:m ≤ u) (ub:u ≤ b)
  (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
local notation "V" => Ψ b
local notation "W" => (H).rep N per b

include simple way D Q ticket π Γ Ψ course top floor ub gate in
theorem original (y:Site ((C).side b per)) (h:Coefficient F ((C).side b per))
    (fmt:h.Format y (C).params V) {M:ℝ} (income:h.remBound y V (LocalComparison.forcedDivisor C b) M)
    (mp:0 ≤ M):WilsonThermometerUnitFilingWhole.RangeCost R (N:=N) (u:=u) (h.density y T V)
        (cost G d (V).p.threshold*(F).coeffSize h.x+5*M):=by
  let source:=h.density y T V
  let hard:=account h V
  let soft:=h.exponentialEntry y T V
  let cap:=cost G d (V).p.threshold*(F).coeffSize h.x
  have quiet:(V).eval=(W).eval:=(QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans ub) top).view
  obtain ⟨hardI,sourceI⟩:=WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course (floor.trans ub) top T (C).params y h fmt income
  have split:source-hard=(fun U=>((W).eval U:ℂ)*soft U):=by
    funext U
    simp only [source,hard,soft,Coefficient.density,account,Pi.sub_apply,sub_eq_add_neg]
    rw [congrFun quiet U];ring
  have price (j:ℕ) (uj:u ≤ j) (jb:j ≤ b):‖reading R (N:=N) source j jb‖ ≤ cap+5*M:=by
    have base:‖reading R (N:=N) (source-hard) j jb‖ ≤ cap+M:=by
      rw [split,WilsonThermometerUnitFilingPosterior.weighted]
      exact actualTransport_norm_le C R.makes top (point R d V h y income) jb 1
    have extra:‖reading R (N:=N) hard j jb‖ ≤ 4*M:=by
      rw [WilsonThermometerUnitFilingRaw.ratio R top V quiet hard jb]
      apply le_of_forall_pos_le_add
      intro δ dp
      have receipt:=WilsonMeasuredOwnerFlatReading.original R simple way D Q ticket π Γ Ψ course top floor ub 0
        (zero_lt_one:0<(1:ℝ)) le_rfl gate T (C).params y h fmt income
        (show 0<M+δ/4 by linarith) (show M ≤ M+δ/4 by linarith) uj jb
      simp only [div_one,mul_one,pow_zero] at receipt
      linarith only [receipt]
    have sum:=WilsonThermometerUnitFilingRaw.add R (N:=N) (source-hard) hard (sourceI.sub hardI) hardI jb
    rw [sub_add_cancel] at sum
    rw [sum]
    exact (norm_add_le ..).trans (by linarith only [base,extra])
  exact ⟨price,fun i j ui uj ib jb=>(norm_sub_le ..).trans (by linarith only [price i ui ib,price j uj jb])⟩

end YM.Integration.WilsonThermometerUnitFilingFieldRange
