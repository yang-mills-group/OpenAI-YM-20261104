import YM.Integration.WilsonForestRetainedChart
import YM.Integration.WilsonForestMarginal

/-! A retained action on the occupied links, integrated with the original
exterior marginal. The only price multiplies the true localized first moment. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonForestRetainedLaw
open Function Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open WilsonPhysicalRegisteredForestAction OriginalMarkedRunAction
open WilsonForestMarginal
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "k" => (j+1)
local notation "op" => R.family.path.levels.clock.op j per
local notation "fine" => Config G (R.family.side k per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per k
local notation "held" => WilsonHeldExteriorLaw.weight R N per j

def redraw (T : Forest (op).ratio) (E : Finset T.Free) (V : coarse) (B : Rep G (R.family.side k per))
    (C : Set fine) (H : fine→ℝ) (v : ({e:T.Free | e∉E}:Set T.Free) → G.El) : ℝ :=
  WilsonForestRetainedFibre.mass R (N:=N) T E V (up) v /
    WilsonForestRetainedFibre.mass R (N:=N) T E V B v *
      read T E (C.indicator (fun U=>held V B U*H U)) v

theorem factor (T : Forest (op).ratio) (E : Finset T.Free) (V : coarse) (B : Rep G (R.family.side k per))
    (C : Set fine) (H : fine→ℝ) (v : ({e:T.Free | e∉E}:Set T.Free) → G.El) :
    read T E (C.indicator (fun U=> WilsonForestRetainedFibre.corrected R (N:=N) T E V B v U*H U)) v =
      redraw R (N:=N) T E V B C H v := by
  unfold redraw WilsonForestMarginal.read
  rw [←integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun x=> ?_))
  by_cases h : filled (S:=op) (G:=G) T E v x ∈ C
  · simp only [Set.indicator_of_mem h,WilsonForestRetainedFibre.corrected,div_eq_mul_inv]
    ac_rfl
  · simp only [Set.indicator_of_notMem h,mul_zero]

theorem original (T : Forest (op).ratio) (E : Finset T.Free) {d : ℕ} (interior : k<N)
    (A : Comparison R (p:=per) interior d) (S : Support (R.family.side k per)) (tails : ∀ e∈E,e.val.1∈S)
    (V : coarse) (C : Set fine) (mc : MeasurableSet C) (H : fine→ℝ) (eh : Envelope H) :
    let B := approximation R (p:=per) interior d
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (k+1))^(d+1))
    let w := held V (up)
    let ν := Measure.pi (fun _ : ({e:T.Free|e∉E}:Set T.Free)=>G.probHaar)
    |(∫ v,read T E (C.indicator (fun U=>w U*H U)) v ∂ν) -
        (∫ v, redraw R (N:=N) T E V B C H v ∂ν)| ≤
      (Real.exp a-1) * ∫ v,read T E (C.indicator (fun U=>w U*|H U|)) v ∂ν := by
  intro B a w ν
  letI : IsProbabilityMeasure ν := by dsimp [ν];infer_instance
  let x := read T E (C.indicator (fun U=>w U*H U))
  let m := read T E (C.indicator (fun U=>w U*|H U|))
  let y := redraw R (N:=N) T E V B C H
  let b := Real.exp a-1
  have h (v) : |x v-y v| ≤ b*m v := by
    have h' := WilsonForestRetainedChart.group R T E interior A S tails V v C mc H eh
    change |x v - read T E (C.indicator (fun U=>WilsonForestRetainedFibre.corrected R (N:=N) T E V B v U*H U)) v| ≤ b*m v at h'
    rw [factor] at h'
    exact h'
  obtain ⟨c,hc,mn⟩ := OriginalMarkedGibbsAction.retained_floor R interior A
  have ep := (WilsonHeldExteriorLaw.regularity R N per j interior.le V B
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hc mn).1
  obtain ⟨t,ht,lower⟩ := WilsonHeldExteriorLaw.upper_floor R N per j interior.le
  have eq := (WilsonHeldExteriorLaw.regularity R N per j interior.le V (up)
    ((up).envelope (R.makes.wilson.represents N per k interior.le).good) ht lower).1
  have eabs : Envelope (fun U=>|H U|) :=
    ⟨eh.meas.abs,eh.cost.choose,fun U=>by simpa only [Real.norm_eq_abs,abs_abs] using eh.cost.choose_spec U⟩
  have env (f : fine→ℝ) (ef : Envelope f) : Envelope (read T E (C.indicator f)) :=
    bounded T E (Envelope.piece mc ef (Envelope.const 0))
  have ix : Integrable x ν := (env _ (eq.mul eh)).integrable ν
  have im : Integrable m ν := (env _ (eq.mul eabs)).integrable ν
  have my : Measurable y := ((bounded T E eq).meas.div (bounded T E ep).meas).mul
    (env _ (ep.mul eh)).meas
  have dom (v) : ‖y v‖ ≤ b*m v + ‖x v‖ := by
    calc ‖y v‖ = ‖(y v-x v)+x v‖ := by rw [sub_add_cancel]
         _ ≤ ‖y v-x v‖+‖x v‖ := norm_add_le _ _
         _ ≤ b*m v+‖x v‖ := add_le_add (by rw [Real.norm_eq_abs,abs_sub_comm];exact h v) le_rfl
  have iy : Integrable y ν := ((im.const_mul b).add ix.norm).mono' my.aestronglyMeasurable (ae_of_all _ dom)
  change |(∫ v,x v ∂ν)-(∫ v,y v ∂ν)| ≤ b*∫ v,m v ∂ν
  rw [←integral_sub ix iy,←integral_const_mul,←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (im.const_mul b)
  exact ae_of_all _ (fun v=>by simpa only [Real.norm_eq_abs] using h v)

end YM.Integration.WilsonForestRetainedLaw
