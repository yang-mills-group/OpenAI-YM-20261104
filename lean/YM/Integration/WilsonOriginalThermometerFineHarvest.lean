import YM.Integration.WilsonOriginalThermometerFineCover
import YM.Integration.WilsonLocalCompactClock

/-! Price a newly joined component all the way to the physical reporter.
Each later step may spend a fixed power of its own temperature. The assigned
distance is available on the original three separated compact source cells
even at arbitrarily remote ultraviolet dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerFineHarvest
open Filter Set MeasureTheory Lattice Wilson RG Source Pressure Extraction PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalThermometerCells WilsonOriginalThermometerFineCover
open scoped Topology BigOperators Classical ContDiff

variable {G:Gauge} (R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta

def bill (k h q m i:ℕ) := k*(i-m+1)+h+q+2

private theorem fourth {x:ℝ} (hx:0≤x) : (1+x)^4≤256*Real.exp x := by
  have one:1+x≤4*Real.exp (x/4) := by linarith only [Real.add_one_le_exp (x/4)]
  have p:=pow_le_pow_left₀ (show 0≤1+x by positivity) one 4
  rw [mul_pow,← Real.exp_nat_mul] at p
  convert p using 1 <;> norm_num <;> first | ring | rfl

private theorem span (simple:G.Simple) (k h q m i:ℕ) (hi:m ≤ i) :
    let b:=radiusB (β i)
    R.family.S.a i*(depth R (bill k h q m i) m i*(4*b+2)+2*b+2:ℕ) ≤
      (20*256*((k+h+q+4:ℕ):ℝ)*(2+G.slopeConstant)^3)*R.family.S.a m*(1+Real.log (β m))^3 := by
  let t:=gap R m i
  let u:=1+Real.log (β m)
  let g:=2+G.slopeConstant
  let K:=((k+h+q+4:ℕ):ℝ)
  have inc:(i-m:ℕ)≤t := RG05Readout.Many.tall (C:=R.family) m i hi
  have tp:0≤t := (show (0:ℝ)≤(i-m:ℕ) by positivity).trans inc
  have a:0≤(k:ℝ):=by positivity
  have hc:0≤(h:ℝ):=by positivity
  have qc:0≤(q:ℝ):=by positivity
  have cap:((bill k h q m i:ℕ):ℝ)+2≤K*(1+t) := by
    dsimp [bill,K]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left inc a,mul_nonneg hc tp,mul_nonneg qc tp,tp]
  have gp:0≤g:=by dsimp [g];linarith [(Gauge.slopeConstant_pos simple).le]
  have up:0≤u:=by dsimp [u];linarith [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have ki:0≤K:=by dsimp [K];positivity
  have ap:0<R.family.S.a i:=R.family.S.a_pos i
  have expEq:R.family.S.a i*Real.exp t=R.family.S.a m := by
    dsimp [t,gap,Schedule.scale]
    rw [Real.exp_sub,Real.exp_log (inv_pos.mpr ap),Real.exp_log (inv_pos.mpr (R.family.S.a_pos m))]
    field_simp [ap.ne',(R.family.S.a_pos m).ne']
  intro b
  apply (mul_le_mul_of_nonneg_left (raw R simple (show 0≤(bill k h q m i:ℝ) by positivity) hi) ap.le).trans
  have start:=mul_le_mul_of_nonneg_right cap
    (show 0≤R.family.S.a i*(20*(g*u*(1+t))^3) by positivity)
  have last:=mul_le_mul_of_nonneg_left (fourth tp)
    (show 0≤R.family.S.a i*(20*K*g^3*u^3) by positivity)
  change R.family.S.a i*(20*(_+2)*(g*u*(1+t))^3) ≤ _
  calc
    _ = (((bill k h q m i:ℕ):ℝ)+2)*(R.family.S.a i*(20*(g*u*(1+t))^3)) := by ring
    _ ≤ _ := start
    _ = R.family.S.a i*(20*K*g^3*u^3)*(1+t)^4 := by ring
    _ ≤ _ := last
    _ = (20*256*K*g^3)*(R.family.S.a i*Real.exp t)*u^3 := by ring
    _ = _ := by rw [expEq]

theorem cells (simple:G.Simple) (φ:Test 3) (legal:tsupport φ⊆conf 3) (k h q:ℕ) :
    ∃p₀:ℕ,∀ᶠ m:ℕ in atTop,∀ p ≥ p₀,∀ (N i:ℕ) (_:m ≤ i) (top:i≤N) (r:ℝ), 0<r → r≤1 →
    R.family.S.a m*(RG16.Lambda R.family.path.levels m)^4≤r →
    ∀ z:Fin 3→Site (R.family.side N p),weight φ (positions (R:=R) r (N,p)) z≠0 →
    ∀v w, v≠w → ∀ B:ℕ,B≤2*radiusB (β i) → depth R (bill k h q m i) m i*(4*B+2)+2*B ≤
      separation ((R.family.S.toDepth top p).parent (z v)) ((R.family.S.toDepth top p).parent (z w)) := by
  obtain ⟨c,cp,score⟩:=WilsonOriginalThermometerFineCells.actual R φ legal
  obtain ⟨p₀,scored⟩:=eventually_atTop.1 score
  let K:ℝ:=2*20*256*((k:ℝ)+h+q+4)*(2+G.slopeConstant)^3
  have sp:0≤G.slopeConstant:=(Gauge.slopeConstant_pos simple).le
  have kp:0≤K:=by dsimp [K];positivity
  have grow:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  refine ⟨p₀,?_⟩
  filter_upwards [grow.eventually_ge_atTop (K/c)] with m big p room N i hi top r rp cap mesh z live v w off B charge
  apply scored p room N i top r rp cap z live v w off
  have native:=span R simple k h q m i hi
  let L:=Real.log (β m)
  have lp:0≤L:=Real.log_nonneg (R.family.path.levels.fits.delayed m).le
  have gauge:(1+L)^3≤(2+L)^3 :=pow_le_pow_left₀ (by positivity) (by linarith) 3
  have cm:K≤c*(2+L):=by have val:K≤L*c:=(div_le_iff₀ cp).mp big;linarith only [cp,val]
  have target:K*(1+L)^3≤c*(2+L)^4:=calc
    _≤K*(2+L)^3:=mul_le_mul_of_nonneg_left gauge kp
    _≤(c*(2+L))*(2+L)^3:=mul_le_mul_of_nonneg_right cm (by positivity)
    _=_:=by ring
  have folded:=mul_le_mul_of_nonneg_left target (R.family.S.a_pos m).le
  have tail:=mul_le_mul_of_nonneg_right mesh cp.le
  have finer:=R.family.S.strictAnti.antitone top
  push_cast at native ⊢
  change R.family.S.a m*(2+L)^4*c ≤ r*c at tail
  let d:=depth R (bill k h q m i) m i
  let b:=radiusB (β i)
  have bnd : (B:ℝ)≤2*(b:ℝ):=by exact_mod_cast charge
  have dp:0≤(d:ℝ):=by positivity
  have expand: (d:ℝ)*(4*(B:ℝ)+2)+2*(B:ℝ)+2≤2*((d:ℝ)*(4*(b:ℝ)+2)+2*(b:ℝ)+2):=by
    nlinarith only [bnd,mul_le_mul_of_nonneg_left bnd dp,dp]
  have scaled:=mul_le_mul_of_nonneg_left expand (R.family.S.a_pos i).le
  change R.family.S.a i*((d:ℝ)*(4*(B:ℝ)+2)+2*(B:ℝ))+2*R.family.S.a N≤r*c
  change R.family.S.a i*((d:ℝ)*(4*(b:ℝ)+2)+2*(b:ℝ)+2)≤_ at native
  dsimp [K] at folded
  nlinarith only [native,folded,tail,finer,scaled]

private theorem geometric (m n:ℕ) :
    Real.exp (-gap R m (m+n)) ≤ Real.exp (-1:ℝ)^n := by
  have bydate: (n:ℝ)≤gap R m (m+n) := by
    simpa only [Nat.add_sub_cancel_left,gap] using (RG05Readout.Many.tall (C:=R.family) m (m+n) (Nat.le_add_right m n))
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  linarith

theorem summed (simple:G.Simple) (k h q m M:ℕ) (a:ℕ→ℝ) (paid:∀i,8≤a i) :
    ∑j∈Finset.range M, (β (m+j))^(k*(m+j-m+1)) * Real.exp ((h:ℝ)*gap R m (m+j)) *
        Real.exp (-(a (m+j)/8)*depth R (bill k h q m (m+j)) m (m+j)) ≤
      (1-Real.exp (-1:ℝ))⁻¹*((β m)^q)⁻¹ := by
  have big:0<β m :=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have charge:0≤((β m)^q)⁻¹:=by positivity
  calc
    _≤∑ j∈Finset.range M,((β m)^q)⁻¹*Real.exp (-1:ℝ)^j := by
      apply Finset.sum_le_sum;intro j _
      apply (price R simple (k*(m+j-m+1)) h q (Nat.le_add_right m j) (paid (m+j))).trans
      exact mul_le_mul_of_nonneg_left (geometric R m j) charge
    _= ((β m)^q)⁻¹*∑j∈Finset.range M,Real.exp (-1:ℝ)^j :=(Finset.mul_sum ..).symm
    _≤((β m)^q)⁻¹*(1-Real.exp (-1:ℝ))⁻¹:=by
      apply mul_le_mul_of_nonneg_left _ charge
      exact sum_le_hasSum (Finset.range M) (fun j _=>pow_nonneg (Real.exp_pos _).le j)
        (hasSum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num)))
    _=_:=mul_comm _ _

theorem tested (simple:G.Simple) (φ:Test 3) (r:ℝ) (N p m M k h q:ℕ) (a:ℕ→ℝ) (paid:∀i,8≤a i)
    (fee:ℝ) (fp:0≤fee)
    (E:ℕ→(Fin 3→Site (R.family.side N p))→ℂ)
    (at_join:∀j∈Finset.range M,∀z,weight φ (positions (R:=R) r (N,p)) z≠0 →
      ‖E j z‖ ≤ fee * ((β (m+j))^(k*(m+j-m+1)) * Real.exp ((h:ℝ)*gap R m (m+j)) *
        Real.exp (-(a (m+j)/8)*depth R (bill k h q m (m+j)) m (m+j)))) :
    ‖∑ j∈Finset.range M,∑z,weight φ (positions (R:=R) r (N,p)) z*E j z‖ ≤
      (∫ x:Points 3,‖φ x‖)*fee*((1-Real.exp (-1:ℝ))⁻¹*((β m)^q)⁻¹) := by
  let cut:=positions (R:=R) r (N,p)
  let F:=fun j:ℕ=>(β (m+j))^(k*(m+j-m+1))*Real.exp ((h:ℝ)*gap R m (m+j))*
    Real.exp (-(a (m+j)/8)*depth R (bill k h q m (m+j)) m (m+j))
  let c:=∫ x:Points 3,‖φ x‖
  have pos : 0≤c:= by dsimp [c];apply MeasureTheory.integral_nonneg; intro x;exact norm_nonneg _
  have ok (j:ℕ):0≤F j:=by
    dsimp only [F]
    have hb:0≤β (m+j):=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
    positivity
  have mass:=variation φ cut (placed (R:=R) r (N,p))
  have priced (j:ℕ) (inside:j∈Finset.range M) :
      ‖∑ z,weight φ cut z*E j z‖≤c*fee*F j := calc
    _ ≤ ∑ z,‖weight φ cut z*E j z‖ := norm_sum_le _ _
    _ ≤ ∑ z,‖weight φ cut z‖*(fee*F j) := by
      apply Finset.sum_le_sum;intro z _
      by_cases live:weight φ cut z=0
      · simp [live]
      · rw [norm_mul];exact mul_le_mul_of_nonneg_left (at_join j inside z live) (norm_nonneg _)
    _ = (∑ z,‖weight φ cut z‖)*(fee*F j) := (Finset.sum_mul ..).symm
    _ ≤ c*(fee*F j) := mul_le_mul_of_nonneg_right mass (mul_nonneg fp (ok j))
    _ = _ := by ring
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑j∈Finset.range M,c*fee*F j := Finset.sum_le_sum priced
    _ = c*fee*∑j∈Finset.range M,F j := (Finset.mul_sum ..).symm
    _ ≤ _:=mul_le_mul_of_nonneg_left (summed R simple k h q m M a paid) (mul_nonneg pos fp)

end YM.Integration.WilsonOriginalThermometerFineHarvest
end
