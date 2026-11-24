import YM.Integration.WilsonMeasuredWindow
import YM.Integration.WilsonIndependentConditionedBankBerth
import YM.Integration.WilsonMovingForkSlotDate

/-! The least unweighted reporting station for a real spatial radius. Its
actual last block pays changes of normalized position or derivative scale. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSpatialHost
open Filter Set Real Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato Asymptotics
open GapsContact.Seams Next.Rank
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "B" => R.family.S.block

def date (r:ℝ):ℕ:=WilsonMeasuredWindow.stop R.family.path.levels simple 0 r

theorem fits {r:ℝ}(pos:0 < r):a (date R simple r) ≤ r:=by
  simpa only [date,pow_zero,mul_one] using WilsonMeasuredWindow.stop_spec R.family.path.levels simple 0 pos

theorem first {r:ℝ}{f:ℕ}(pos:0 < r)(seen:a f ≤ r):date R simple r ≤ f:=by
  unfold date WilsonMeasuredWindow.stop
  rw [dif_pos pos]
  exact Nat.find_min' _ (by simpa only [pow_zero,mul_one] using seen)

theorem late:Tendsto (date R simple) (𝓝[>] (0:ℝ)) atTop:=by
  refine tendsto_atTop.mpr fun f=>?_
  have tiny:∀ᶠ r:ℝ in 𝓝[>] 0,r < a f:=
    (eventually_lt_nhds (R.family.S.a_pos f)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,tiny] with r pos fit
  exact le_of_not_gt fun earlier=>
    (not_lt_of_ge ((R.family.S.strictAnti.antitone earlier.le).trans (fits R simple pos))) fit

theorem last {r:ℝ}(pos:0 < r)(narrow:r < a 0):
    let m:=date R simple r
    0 < m ∧ a m ≤ r ∧ r < a (m-1) ∧ 1 ≤ r/a m ∧ r/a m < ((B (m-1)).val:ℝ):=by
  intro m
  have hit:=fits R simple pos
  have nonzero:0 < m:=by
    by_contra! h
    change a m ≤ r at hit
    rw [Nat.le_zero.mp h] at hit
    exact (not_lt_of_ge hit) narrow
  have older:r < a (m-1):=lt_of_not_ge (fun before=>by
    have prior:m ≤ m-1:=first R simple pos before
    omega)
  have step:=R.family.S.embeds_scale (R.family.S.oneStep (m-1) 0)
  change a ((m-1)+1)*((B (m-1)).val:ℝ)=a (m-1) at step
  rw [Nat.sub_add_cancel nonzero] at step
  refine ⟨nonzero,hit,older,(one_le_div (R.family.S.a_pos _)).2 hit,?_⟩
  exact (div_lt_iff₀ (R.family.S.a_pos _)).2 (older.trans_eq (step.symm.trans (mul_comm ..)))

include simple in
theorem block (slow:WilsonWindowReportingPace.Slow R.kit)(p:ℕ){ε:ℝ}(positive:0<ε):
    ∀ᶠ j:ℕ in atTop,((B j).val:ℝ) ≤ 1+log (log (β j)) ∧ (1+((B j).val:ℝ))^p ≤ (β j)^ε:=by
  let θ:=ε/((p:ℝ)+1)
  have theta:0<θ:=div_pos positive (by positivity)
  have hot:=Station.hat_rate R.family.path.levels simple
  have warm:=Real.tendsto_log_atTop.comp hot
  have cash:=hot.eventually ((isLittleO_log_rpow_atTop theta).bound (c:=1/2) (by norm_num))
  filter_upwards [warm.eventually_ge_atTop 2,cash] with j large flow
  have l:2 ≤ log (β j):=large
  have bl:0<log (β j):=by linarith only [l]
  have bpos:0<β j:=zero_lt_one.trans (R.family.path.levels.fits.delayed j)
  have bound:((B j).val:ℝ) ≤ 1+log (log (β j)):=by
    have step:=slow.2 j
    change ((B j).val:ℝ) ≤ log (2+log (β j)) at step
    have widen:log (2+log (β j)) ≤ log (2*log (β j)):=log_le_log (by linarith only [l]) (by linarith only [l])
    rw [log_mul (by norm_num: (2:ℝ)≠0) bl.ne'] at widen
    linarith only [step,widen,log_le_sub_one_of_pos (by norm_num:0<(2:ℝ))]
  have grow:log (β j) ≤ (1/2:ℝ)*(β j)^θ:=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg bpos.le θ)] using flow)
  have estimate:1+((B j).val:ℝ) ≤ (β j)^θ:=by
    linarith only [bound,log_le_sub_one_of_pos bl,l,grow]
  have ep:θ*(p:ℝ) ≤ ε:=by
    have unit:θ*((p:ℝ)+1)=ε:=div_mul_cancel₀ _ (by positivity)
    nlinarith only [theta,unit]
  refine ⟨bound, (pow_le_pow_left₀ (by positivity) estimate p).trans ?_⟩
  rw [←Real.rpow_natCast ((β j)^θ) p,←Real.rpow_mul bpos.le]
  exact Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed j).le ep

theorem root (slow:WilsonWindowReportingPace.Slow R.kit)(p:ℕ){ε:ℝ}(positive:0<ε):
    ∀ᶠ r in 𝓝[>] (0:ℝ),let m:=date R simple r
    0 < r ∧ 0 < m ∧ a m ≤ r ∧ r < a (m-1) ∧ 1 ≤ r/a m ∧ r/a m < ((B (m-1)).val:ℝ) ∧
    ((B (m-1)).val:ℝ) ≤ 1+log (log (β (m-1))) ∧
    ∀f,m ≤ f → (1+r/a m)^p ≤ (1+((B (m-1)).val:ℝ))^p ∧ (1+((B (m-1)).val:ℝ))^p ≤ (β f)^ε:=by
  have old:Tendsto (fun r=>date R simple r-1) (𝓝[>] (0:ℝ)) atTop:=by
    refine tendsto_atTop.mpr fun n=>?_
    filter_upwards [(late R simple).eventually_ge_atTop (n+1)] with r age
    omega
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds,
    old.eventually (block R simple slow p positive)] with r pos tiny fee
  intro m
  have bill:=last R simple pos tiny
  refine ⟨pos,bill.1,bill.2.1,bill.2.2.1,bill.2.2.2.1,bill.2.2.2.2,fee.1,fun f after=>⟨?_,?_⟩⟩
  · exact pow_le_pow_left₀ (by have rg:=bill.2.2.2.1;change 1 ≤ r/a m at rg;linarith) (add_le_add_right bill.2.2.2.2.le 1) _
  · exact fee.2.trans (Real.rpow_le_rpow (zero_le_one.trans (R.family.path.levels.fits.delayed (m-1)).le)
      (OPE.Log.beta_mono simple ((Nat.sub_le m 1).trans after)) positive.le)

end YM.Integration.WilsonIndependentConditionedGramSpatialHost
