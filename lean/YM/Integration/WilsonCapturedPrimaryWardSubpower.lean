import YM.Integration.WilsonCapturedPrimaryWardPaidHorizon

/-! Arbitrary fixed inverse-coupling and occupied source wages under the physical spatial gap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonCapturedPrimaryWardSubpower
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels OPE OPE.Cards RG12
open RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof Ribbons ManyCopies Accent
open Filter Function Lattice Wilson RG OPE RG16.Literal MergeProof Ribbons Bid PhysMS
open OPE.Log Trace.Pilot
open Extra.Histories PhysicalNext.Repeat.Legato Bandage Push Trace.Physical.GermGraph WilsonReflectedPhysicalRate
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple)

private theorem exp_radius {r:ℝ} (rp:0<r) (a:ℝ) :
    Real.exp ((-a)*LogV r)=r^a:=by
  rw [Real.rpow_def_of_pos rp]
  unfold LogV
  rw [Real.log_inv]
  congr 1
  ring

theorem decay (slow:WilsonWindowReportingPace.Slow R.kit) (v:ℕ) (grow:0<v) (h q:ℕ) :
    ∀ᶠ r in trail,let β:=R.family.path.levels.clock.hatBeta (launch R simple v r)
      0<β ∧ (1+β)^q*r^((h:ℝ)+1/32)  ≤  r^((h:ℝ)+1/64):=by
  let β:ℝ→ℝ:=fun r=>R.family.path.levels.clock.hatBeta (launch R simple v r)
  have time:=PhysMS.to_log_zoom
  have base:RateIs trail LogV β 0:=height0 (hut R.family simple) (dates R simple slow v grow).2
  have scale:RateIs trail LogV (fun r=>(1+β r)^q) 0:=
    (((RateIs.const (c:=1) time one_pos).add base time).power q).swap (by simp)
  have pay:=scale.mul (RateIs.exp (-((h:ℝ)+1/32)) time)
  have bound:=(RateIs.exp (-((h:ℝ)+1/64)) time).overtakes (pay.pays time) time (by linarith)
  filter_upwards [self_mem_nhdsWithin,base.pos,bound] with r pos hot rate
  have rp:0<r:=pos
  exact ⟨hot,(by simpa only [exp_radius rp] using rate.le)⟩

def constant (E:ℝ) (fee:Fin 3→ℝ):ℝ:=1+2*(abs E)*∑i,(abs (fee i))

theorem face (b E:ℝ) (fee:Fin 3→ℝ) (s:Finset (Fin 3)) (hot:0 ≤ b) :
    (∏i∈s,(1+E*(2*b)*fee i))*2^(3-s.card)  ≤  8*(constant E fee)^3*(1+b)^3:=by
  let M:=constant E fee
  have cp:(1:ℝ) ≤ M:=le_add_of_nonneg_right (by positivity)
  have big:(1:ℝ)  ≤  M*(1+b):=one_le_mul_of_one_le_of_one_le cp (by linarith)
  have entries(i:Fin 3):|1+E*(2*b)*fee i|  ≤  M*(1+b):=by
    have total:(abs (fee i)) ≤ ∑j,(abs (fee j)):=single_le_sum (fun j _=>abs_nonneg (fee j)) (mem_univ i)
    have m:2*(abs E)*(abs (fee i)) ≤ 2*(abs E)*∑j,(abs (fee j)):=mul_le_mul_of_nonneg_left total (by positivity)
    calc
      _  ≤  |(1:ℝ)|+|E*(2*b)*fee i|:=abs_add_le .. 
      _ = 1+(2*(abs E)*(abs (fee i)))*b:=by rw [abs_one,abs_mul,abs_mul,abs_mul,abs_of_nonneg hot];norm_num;ring
      _  ≤  M*(1+b):=by dsimp [M,constant];nlinarith [mul_le_mul_of_nonneg_right m hot,abs_nonneg E,
        show 0 ≤ ∑j,(abs (fee j)) from sum_nonneg (fun j _=>abs_nonneg (fee j))]
  have factors:(∏i∈s,(1+E*(2*b)*fee i))  ≤  (M*(1+b))^3:=by
    calc
      _  ≤  |∏i∈s,(1+E*(2*b)*fee i)|:=le_abs_self _
      _ = ∏i∈s,|1+E*(2*b)*fee i|:=Finset.abs_prod _ _
      _  ≤  ∏_i∈s,M*(1+b):=Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>entries i)
      _ = (M*(1+b))^s.card:=by simp
      _  ≤  _:=pow_le_pow_right₀ big (by simpa using card_le_univ s)
  have step:(2:ℝ)^(3-s.card) ≤ 8:=by calc
    _  ≤  (2:ℝ)^3:=pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    _ = _:=by norm_num
  exact (mul_le_mul factors step (by positivity) (by positivity)).trans_eq (by rw [mul_pow];ring)

theorem aggregate {b r E K B:ℝ} (fee:Fin 3→ℝ) (c:Finset (Fin 3)→ℂ) (h q:ℕ)
    (hot:0≤b) (rp:0≤r) (kp:0≤K) (bp:0≤B)
    (budget:(∑s,‖c s‖)≤B*(1+b)^q)
    (gap:(1+b)^(q+3)*r^((h:ℝ)+1/32)≤r^((h:ℝ)+1/64)) :
    (∑s,‖c s‖*(((∏i∈s,(1+E*(2*b)*fee i))*2^(3-s.card))*(K*r^((h:ℝ)+1/32))))
      ≤ 8*B*K*constant E fee^3*r^((h:ℝ)+1/64):=by
  let T:=8*constant E fee^3*(1+b)^3*(K*r^((h:ℝ)+1/32))
  have cp:0≤constant E fee:=by unfold constant;positivity
  have zp:0≤T:=by dsimp [T];positivity
  calc
    _ ≤ ∑s,‖c s‖*T:=sum_le_sum fun s _=>mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (face b E fee s hot) (by positivity)) (norm_nonneg _)
    _ = (∑s,‖c s‖)*T:=(Finset.sum_mul ..).symm
    _ ≤ B*(1+b)^q*T:=mul_le_mul_of_nonneg_right budget zp
    _ = 8*B*K*constant E fee^3*((1+b)^(q+3)*r^((h:ℝ)+1/32)):=by dsimp [T];rw [pow_add];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left gap (by positivity)

end YM.Integration.WilsonCapturedPrimaryWardSubpower

