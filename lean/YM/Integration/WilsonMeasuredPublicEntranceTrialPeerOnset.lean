import YM.Integration.WilsonMeasuredPublicEntranceCropClock
import YM.Integration.WilsonMeasuredPublicEntranceCropLedger
import YM.Integration.WilsonThermometerUnitFilingChartFee

/-! Prices for all mixtures of the posted trial fields and physical signed
fields, before either regulator, on the actual shared course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialPeerOnset
open Filter Finset Lattice Wilson RG Labels Source Marker QuadraticLocal
open PhysicalNext PhysicalNext.Repeat Legato Extra.Histories
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset Pressure ConnectedActivityE6
open WilsonMeasuredPublicEntranceCropClock WilsonThermometerUnitFilingFieldRange
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V → ℕ)
local notation "A" => R.family.path.levels

def wide (t:ℕ)(C:ℝ) := max C (((∑i,d i)+t+2:ℕ):ℝ)
theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (A))(n t l:ℕ)(size:Fintype.card V ≤ n)(C:ℝ)(cp:0 ≤ C):
    ∀ᶠ f:ℕ in atTop,∀(N p m k:ℕ)(_mf:m ≤ f)(_fn:f ≤ N)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)
    (Ψ:∀i,Rep G (R.family.side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ → ((A).params f).supportExponent=100 →
    ∀(o:V → Site (R.family.side f p))(q:∀v,Coefficient (R.family.labels.level (d v)) (R.family.side f p))
      (B w:V → ℝ)(trial:Finset V),
    let H:=(A).clock.hatBeta f
    let P:=R.family.path.rep N p f
    let C':=wide d t C
    let U:=C'*span H
    let D:=WilsonMeasuredPublicEntranceCropRate.depth n l H U
    let Vmax:=fee n l t C' H
    let μ:=fun i=>if i∈trial then 1/w i else cost G (d i) P.p.threshold*
      (R.family.labels.level (d i)).coeffSize (q i).x+B i
    (∀v,0 ≤ B v) → (∀v,0 < w v ∧ w v ≤ 1) →
    (∀v,WilsonSeparatedPrefixCanonicalMounted.salary R d f p q B v ≤ H^t) →
    (∀v,(w v)⁻¹ ≤ Real.exp (C*span H)) →
    C*span H ≤ U ∧ 0 ≤ U ∧ 1 ≤ Vmax ∧ (∀v,μ v ≤ Real.exp U ∧ B v ≤ Real.exp U ∧ (w v)⁻¹ ≤ Real.exp Vmax) ∧
    WilsonMeasuredPublicEntranceTrialPeerBoard.price (N:=N) R d o (Ψ f) q trial w (fun _=>D) B 1 ≤ Real.exp Vmax ∧
    ∀(b:ℕ)(gap:ℝ),((f-b:ℕ):ℝ) ≤ gap*(1+Real.log H)^4 →
      ((f-b+Nat.ceil (2*Vmax):ℕ):ℝ) ≤ (gap+2*capital n l t C'+1)*(1+Real.log H)^4:=by
  have headings:∀ᶠ f:ℕ in atTop,∀v:V,6+basisCost G (d v) ≤ (A).clock.hatBeta f:=
    Filter.eventually_all.mpr (fun v=>(RG01.Physical.hats simple (A)).eventually_ge_atTop _)
  filter_upwards [WilsonMeasuredPublicEntranceCropLedger.original R d simple pace book,headings,
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp (RG01.Physical.hats simple (A))).eventually_ge_atTop 1] with f ledger heads one logp
  intro N p m k mf fn π Γ Ψ course support o q B w trial H P C' U D Vmax μ bn width salary owned
  have logH:1 ≤ Real.log H:=logp
  have level:1 ≤ H:=by linarith only [one]
  have hpos:0 < H:=zero_lt_one.trans_le level
  have cc:0 ≤ C':=cp.trans (le_max_left ..)
  have stats:=WilsonMeasuredPublicEntranceCropClock.original n l t C' H cc level logp
  have scale:1 ≤ WilsonThermometerMixedCollarSubpower.scale H:=by
    unfold WilsonThermometerMixedCollarSubpower.scale;linarith only [le_max_left 0 (Real.log (Real.log H))]
  have hor:Real.log H ≤ span H:=by
    have t:=le_mul_of_one_le_right (show 0 ≤ 1+Real.log H by linarith only [logH]) (one_le_pow₀ (n:=3) scale)
    dsimp only [span];linarith only [t]
  have sp:0 ≤ span H:=(Real.log_nonneg level).trans hor
  have before:C*span H ≤ U:=mul_le_mul_of_nonneg_right (le_max_left ..) sp
  have uj:0 ≤ U:=mul_nonneg cc sp
  have point:(Ψ f).p=P.p:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course mf fn).1.symm
  have date:(Ψ f).p=(A).budget f:=point.trans (R.makes.wilson.represents N p f fn).vac
  have held (t₀:ℕ)(small:(t₀:ℝ) ≤ C'):H^t₀ ≤ Real.exp U:=by
    have cab:=mul_le_mul small hor (Real.log_nonneg level) cc
    rw [←Real.exp_log hpos,←Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr cab
  refine ⟨before,uj,stats.1,?_,?_,stats.2.2.2 f⟩
  · intro v
    let F:=R.family.labels.level (d v)
    have full:=salary v
    change H^6*F.coeffSize (q v).x+H^2*B v ≤ H^t at full
    have xn:0 ≤ F.coeffSize (q v).x:=Finset.sum_nonneg fun _ _=>norm_nonneg _
    have aa:=le_mul_of_one_le_left xn (one_le_pow₀ (n:=6) level)
    have bb:=le_mul_of_one_le_left (bn v) (one_le_pow₀ (n:=2) level)
    have xb:F.coeffSize (q v).x ≤ H^t:=by linarith only [full,aa,bb,bn v]
    have gross:B v ≤ H^t:=by linarith only [full,aa,bb,xn]
    have term:d v ≤ ∑i,d i:=Finset.single_le_sum (fun i _=>Nat.zero_le (d i)) (Finset.mem_univ v)
    have high:((d v+t+2:ℕ):ℝ) ≤ C':=
      (show ((d v+t+2:ℕ):ℝ) ≤ (((∑i,d i)+t+2:ℕ):ℝ) by exact_mod_cast (Nat.add_le_add_right (Nat.add_le_add_right term t) 2)).trans (le_max_right ..)
    have sm:(t:ℝ) ≤ C':=by push_cast at high;linarith only [high,(Nat.cast_nonneg (d v):0 ≤ ((d v):ℝ))]
    have inc: H^t ≤ Real.exp U:=held t sm
    have wt:= (owned v).trans (Real.exp_le_exp.mpr before)
    refine ⟨?_,gross.trans inc,wt.trans (Real.exp_le_exp.mpr stats.2.1)⟩
    change (if _ then _ else _) ≤ _
    split
    · simpa only [one_div] using wt
    · have born:=WilsonThermometerUnitFilingChartFee.original R π Γ Ψ course (d v) mf fn
      rw [point] at born
      have slight:=mul_le_mul_of_nonneg_right (heads v) (pow_nonneg hpos.le (d v))
      have pot:cost G (d v) P.p.threshold ≤ H^(d v+1):=by
        rw [pow_succ'];linarith only [born,slight]
      have maxed:=mul_le_mul pot xb xn (pow_nonneg hpos.le _)
      have amount:H^t ≤ H^(d v+1+t):=pow_le_pow_right₀ level (by omega)
      have two:=mul_le_mul_of_nonneg_right one (pow_nonneg hpos.le (d v+1+t))
      apply le_trans _ (held (d v+t+2) high)
      rw [←pow_add] at maxed
      have shape:d v+t+2=(d v+1+t)+1:=by omega
      rw [shape,pow_succ']
      linarith only [maxed,gross,amount,two]
  · have signed:=ledger N p fn (Ψ f) date support o q B w D t trial bn
      (fun v=>⟨(width v).1.le,(width v).2⟩) salary
    have count:(Fintype.card V:ℝ) ≤ (n:ℝ):=by exact_mod_cast size
    exact signed.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right count (Real.exp_pos _).le)
      (pow_nonneg hpos.le t)).trans stats.2.2.1)

end YM.Integration.WilsonMeasuredPublicEntranceTrialPeerOnset
end
