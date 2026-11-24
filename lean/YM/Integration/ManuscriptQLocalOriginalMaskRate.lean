import YM.Integration.ManuscriptQLocalRegularCalendar
import YM.Integration.OriginalForcedFlat
import YM.Integration.ActualNumericShortHulls

/-! Polynomial order of the genuine logged thermal invoice at an original step. -/

noncomputable section
namespace YM.Integration.ManuscriptQLocalRawMaskFlat
open Filter Finset Lattice RG Wilson Marker MeasureTheory Comparison.RG02
open ManuscriptQLocalRegularConditional ManuscriptQLocalRegularCalendar ManuscriptQLocalMeasuredMarkDifference
open scoped Classical BigOperators Topology

private theorem growth {ι : Type} (I : Finset ι) (f : ι→ℂ) (h : ι→ℕ)
    (n : ℕ) (hn : ∀i∈I,h i≤n) {b a x : ℝ} (hb : 0≤b) (ha : 0≤a) (hx : 1≤x)
    (hbase : 1+b≤(1+a)*x) : modulus I f h b ≤ x^n*modulus I f h a := by
  unfold modulus
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi=>?_
  have t := pow_le_pow_left₀ (by linarith : 0≤1+b) hbase (h i)
  rw [mul_pow] at t
  have a₀ := t.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (hn i hi)) (pow_nonneg (by linarith : 0≤1+a) _))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left a₀ (mul_nonneg (norm_nonneg (f i)) (Nat.cast_nonneg (h i)))

def degree (n j : ℕ) := (j+1)*(n*n)+n+6

def constant (n modes j : ℕ) (a σ : ℝ) : ℝ :=
  let v := (modes:ℝ)*expBill n a
  (2*logBill n v)^j*(logMod n v*expMod n a)*(((Fintype.card PlaqAxes*4:ℕ):ℝ)*81/σ*a)

theorem bill (n modes j : ℕ) {b a A σ B κ : ℝ} (hb : 0≤b) (ha : 0≤a) (hA : 1≤A)
    (σpos : 0<σ) (Bpos : 0≤B) (hh : B≤A) (hκ : 0≤κ) (secured : b≤a*A) :
    let v := (modes:ℝ)*expBill n b
    (2*logBill n v)^j*(logMod n v*expMod n b)*
      (((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*B+1)^4*(A/σ)*κ*b) ≤
      constant n modes j a σ*A^(degree n j)*κ := by
  let v := (modes:ℝ)*expBill n b
  let v₀ := (modes:ℝ)*expBill n a
  have h0 := zero_le_one.trans hA
  have hv : 0≤v := mul_nonneg (Nat.cast_nonneg _) (exp_pos _ hb)
  have hv₀ : 0≤v₀ := mul_nonneg (Nat.cast_nonneg _) (exp_pos _ ha)
  have x := one_le_pow₀ (n:=n) hA
  have u : v≤v₀*A^n := by
    simpa only [v,v₀,mul_comm,mul_assoc,mul_left_comm] using
      mul_le_mul_of_nonneg_left ((exp_mono n hb secured).trans (exp_scale n ha hA)) (Nat.cast_nonneg modes)
  have log : logBill n v≤A^(n*n)*logBill n v₀ := by
    simpa only [←pow_mul] using (log_mono n hv u).trans (log_scale n hv₀ x)
  have expm : expMod n b≤A^n*expMod n a := growth _ _ _ n (fun i hi=>Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hb ha hA (by nlinarith only [secured,hA])
  have logm : logMod n v≤A^(n*n)*logMod n v₀ := by
    simpa only [logMod,←pow_mul] using growth (Finset.range n) (fun i=>(-1:ℂ)^i/(i+1:ℂ)) (fun i=>i+1) n
      (fun i hi=>Finset.mem_range.mp hi) (by linarith : 0≤v+1) (by linarith : 0≤v₀+1) x (by nlinarith only [u,x])
  have lo := log_pos n hv
  have l0 := log_pos n hv₀
  have le₀ : 0≤logMod n v := nonnegative _ _ _ (by linarith : 0≤v+1)
  have ee₀ : 0≤expMod n b := nonnegative _ _ _ hb
  have l1 : 0≤logMod n v₀ := nonnegative _ _ _ (by linarith : 0≤v₀+1)
  have e1 : 0≤expMod n a := nonnegative _ _ _ ha
  have blocks : 2*B+1≤3*A := by linarith only [hh,hA]
  have factors : (2*logBill n v)^j ≤ (A^(n*n)*(2*logBill n v₀))^j :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) lo) (by linarith only [log]) _
  have sums := mul_le_mul logm expm ee₀ (mul_nonneg (pow_nonneg h0 _) l1)
  have trees := mul_le_mul factors sums (mul_nonneg le₀ ee₀) (pow_nonneg (mul_nonneg (pow_nonneg h0 _) (mul_nonneg (by norm_num) l0)) _)
  have size := pow_le_pow_left₀ (by linarith : 0≤2*B+1) blocks 4
  have inspected : ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(2*B+1)^4*(A/σ)*κ*b ≤
      ((Fintype.card PlaqAxes*4:ℕ):ℝ)*(3*A)^4*(A/σ)*κ*(a*A) := by gcongr
  calc _ ≤ (A^(n*n)*(2*logBill n v₀))^j*(A^(n*n)*logMod n v₀*(A^n*expMod n a))*
             (((Fintype.card PlaqAxes*4:ℕ):ℝ)*(3*A)^4*(A/σ)*κ*(a*A)) :=
          mul_le_mul trees inspected (by positivity) (by positivity)
       _ = _ := by
          have eq : degree n j=(n*n)*j+(n*n)+n+6 := by unfold degree;ring
          rw [eq,pow_add,pow_add,pow_add,pow_mul,mul_pow]
          unfold constant
          dsimp only [v₀]
          ring

open Function Set MeasureTheory Lattice Wilson RG RG.Shoot OPE.Therm
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm

private theorem constant_nonneg (n modes j : ℕ) {a σ:ℝ} (ha:0≤a) (hs:0≤σ) : 0≤constant n modes j a σ := by
  let v := (modes:ℝ)*expBill n a
  have hv : 0≤v := mul_nonneg (Nat.cast_nonneg modes) (exp_pos n ha)
  have hL := log_pos n hv
  have hℓ : 0≤logMod n v := nonnegative _ _ _ (by linarith : 0≤v+1)
  have he : 0≤expMod n a := nonnegative _ _ _ ha
  dsimp only [constant]
  exact mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hL) _) (mul_nonneg hℓ he))
    (mul_nonneg (div_nonneg (by positivity) hs) ha)

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  (R : Run G) (hG : G.Simple) (W : Poetry R.family.path.levels) {J : Request V} (A : NumericSchedule R.family J)

include hG W

/-- A single cutoff precedes every original datum, every signed admitted
regular packet population and independent test; the averaging remains on
the same actual coarse Wilson scene with its full unmarked gas. -/
theorem physical (j r : ℕ) {ε : ℝ} (hε : 0<ε) : ∀ᶠ m:ℕ in atTop,∀z:LocalFormal.Datum R.family Γ,z.level=m→
    ∀ (F : AnalyticInput J A z) (x : IndependentTests J.tests),
    let g := regulatorRun R.family z.cutoff z.period (z.level+1)
    let p := (R.family.path.rep z.cutoff z.period (z.level+1)).p
    let w := fun v=>F.inputRadii v/F.kernelCosts v
    let X := F.packets.read (testInclusion J.tests x) g
    let Y := ManuscriptQLocalOriginalConditionalTail.source F.packets p g x 1
    let L S := ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=z.cutoff) S
    ∫U,(Poly.price w (L X U-L Y U))^(j+1) ∂scene R.family.path z.cutoff z.period z.level ≤ ε*g^r := by
  let n := Fintype.card V
  let a := (n:ℝ)*(2:ℝ)^J.inputPacketRankCap
  let C := constant n (Fintype.card Γ.Mode) j a J.inputSupport
  have ha : 0≤a := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hC : 0≤C := constant_nonneg _ _ _ ha J.input_support_pos.le
  have h1 : 0<C+1 := by linarith
  obtain ⟨start,aug⟩ := absorb A (degree n j) (r+1) 1 zero_lt_one
  filter_upwards [ManuscriptQLocalRawMaskCalendar.physical R hG W A 1 j,
    (tendsto_add_atTop_nat 1).eventually (OriginalForcedFlat.allowance R hG (r+1) (div_pos hε h1)),
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one),
    eventually_ge_atTop start] with m window realHit weak ready z hz F x
  subst m
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  let cost := A.admittedCost z.level
  let κ := R.family.path.levels.clock.forcedAllowance (z.level+1)
  have k0 : 0≤κ := (Real.exp_pos _).le
  have cg : 0<g := IterationFour.Currency.g_pos R.makes _ _ _ z.below
  have hcost : 1≤cost := A.admitted_cost_ge_one _
  have hw : g≤1 := (weak z.cutoff z.period z.below).le
  let b := (n:ℝ)*((2:ℝ)^F.packets.rankCap*cost)
  have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (zero_le_one.trans hcost))
  have bp : b≤a*cost := by
    simpa only [a,b,mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) F.rank_bounded) (zero_le_one.trans hcost)) (Nat.cast_nonneg n)
  have hp : ((A.inputNorm z.level).B:ℝ)≤cost := by
    have ⟨_,hf⟩ := ActualNumericShortHulls.covers_le_cost A z.level
    rw [(A.input_norm z.level).block]
    exact (le_add_of_nonneg_left zero_le_one).trans hf
  have grade := bill n (Fintype.card Γ.Mode) j hb ha hcost J.input_support_pos (Nat.cast_nonneg _) hp k0 bp
  have thermal := window z rfl F x
  simp only [pow_one,(A.input_norm z.level).reserve] at thermal
  apply thermal.trans (grade.trans ?_)
  have supplied : κ≤(ε/(C+1))*g^(r+1) := realHit z.cutoff z.period z.below
  have charged : cost^(degree n j)*g^(r+1)≤g^r := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast] using
      aug z.level ready z.cutoff z.period z.below cg hw
  have constantPrice : C*(ε/(C+1))≤ε := by
    rw [←mul_div_assoc,div_le_iff₀ h1];nlinarith
  calc C*cost^(degree n j)*κ ≤ C*cost^(degree n j)*((ε/(C+1))*g^(r+1)) :=
         mul_le_mul_of_nonneg_left supplied (mul_nonneg hC (pow_nonneg (zero_le_one.trans hcost) _))
       _ = (C*(ε/(C+1)))*(cost^(degree n j)*g^(r+1)) := by ring
       _ ≤ _ := mul_le_mul constantPrice charged (mul_nonneg (pow_nonneg (zero_le_one.trans hcost) _) (pow_nonneg cg.le _)) hε.le

end YM.Integration.ManuscriptQLocalRawMaskFlat
end

noncomputable section
namespace YM.Integration.ManuscriptQLocalRawSourceGrade
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm
open scoped Classical BigOperators Topology
/-- The unique finite coupled projection used in the remainder is Borel on
the actual field whenever its physical auxiliary values are Borel. -/
theorem projection {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} (q : Ω→Polynomial ℂ) (L : ℂ→Ω→ℂ)
    (hi : ∀z,Measurable (L z)) (hd : ∀U,(q U).natDegree≤D) (he : ∀U z,(q U).eval z=L z U) (k : ℕ) :
    Measurable fun U=>ManuscriptQLocalConditionalGradeTail.low (q U) D k := by
  have coef (i : ZMod (D+1)) : Measurable fun U=>(q U).coeff i.val := by
    have eqn : (fun U=>(q U).coeff i.val) = fun U=>project (fun j:ZMod (D+1)=>L (phase j) U) i := by
      funext U
      simpa only [one_mul,one_pow,he] using (ManuscriptQLocalConditionalGradeTail.scaled (q U) (hd U) 1 i).symm
    rw [eqn]
    simp_rw [ManuscriptQLocalSourceFourier.projection]
    exact Finset.measurable_sum _ fun j _=>(measurable_const (a:=ManuscriptQLocalSourceFourier.weight j i)).smul (hi (phase j))
  unfold ManuscriptQLocalConditionalGradeTail.low
  refine Finset.measurable_sum _ fun i _=>?_
  by_cases h : i.val≤k
  · simp only [if_pos h]
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt] using coef ((i.val:ℕ):ZMod (D+1))
  · simp only [if_neg h];exact measurable_const

end YM.Integration.ManuscriptQLocalRawSourceGrade
end
