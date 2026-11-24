import YM.Integration.WilsonForestRetainedLaw

/-! Transfer the paid retained-action estimate through an exact change of
coordinates on the same occupied forest and its original exterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonForestRetainedIntegral
open Function Set MeasureTheory Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm OriginalMarkedRunAction
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {N per j:ℕ}
local notation "k" => (j+1)
local notation "op" => R.family.path.levels.clock.op j per
local notation "fine" => Config G (R.family.side k per)
local notation "coarse" => Config G (R.family.side j per)
local notation "Q" => R.family.path.rep N per k
local notation "held" => WilsonHeldExteriorLaw.weight R N per j

theorem tested (T:Forest (op).ratio) (E:Finset T.Free) {d:ℕ} (interior:k<N)
    (A:Comparison R (p:=per) interior d) (S:Support (R.family.side k per)) (tails:∀e∈E,e.val.1∈S)
    (V:coarse) (C:Set fine) (mc:MeasurableSet C)
    (chart:(({i:T.Free|i∉E}:Set T.Free)→G.El)→(fine→ℝ)→ℝ)
    (fiber:∀v h,Measurable h→WilsonForestMarginal.read T E (C.indicator h) v=chart v h)
    (total:∀f: fine→ℝ,Envelope f→GaugeInvariant f→ actualAverage R.family (N:=N) (C.indicator f) V =
      ∫v,chart v (fun U=>held V (Q) U*f U) ∂Measure.pi (fun _=>G.probHaar))
    {fee:ℝ} (paid:Real.exp (OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (k+1))^(d+1)))-1≤fee)
    (H:fine→ℝ) (eh:Envelope H) (inv:GaugeInvariant H) :
    let B:=approximation R (p:=per) interior d
    let Z:=WilsonForestRetainedFibre.mass R (N:=N) T E V
    |actualAverage R.family (N:=N) (C.indicator H) V -
       (∫v,Z (Q) v/Z B v*chart v (fun U=>held V B U*H U) ∂Measure.pi (fun _=>G.probHaar))| ≤
      fee*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  intro B Z
  let ν:=Measure.pi (fun _ : ({e:T.Free|e∉E}:Set T.Free)=>G.probHaar)
  let w:=held V (Q)
  have eabs : Envelope (fun U=>|H U|) :=
    ⟨eh.meas.abs,eh.cost.choose,fun U=>by simpa only [Real.norm_eq_abs,abs_abs] using eh.cost.choose_spec U⟩
  have gabs : GaugeInvariant (fun U=>|H U|) := fun g U=>congrArg abs (inv g U)
  obtain ⟨c,hc,mn⟩:=WilsonHeldExteriorLaw.upper_floor R N per j interior.le
  have eq := (WilsonHeldExteriorLaw.regularity R N per j interior.le V (Q)
    ((Q).envelope (R.makes.wilson.represents N per k interior.le).good) hc mn).1
  obtain ⟨b,hb,bm⟩:=OriginalMarkedGibbsAction.retained_floor R interior A
  have eb := (WilsonHeldExteriorLaw.regularity R N per j interior.le V B
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hb bm).1
  have trueRow (h:fine→ℝ) (e:Envelope h) (g:GaugeInvariant h) :
      actualAverage R.family (N:=N) (C.indicator h) V =
      ∫v, WilsonForestMarginal.read T E (C.indicator (fun U=>w U*h U)) v ∂ν := by
    exact (total h e g).trans (integral_congr_ae (ae_of_all _ fun v=>
      (fiber v (fun U=>w U*h U) (eq.meas.mul e.meas)).symm))
  have drawn:(∫v,WilsonForestRetainedLaw.redraw R (N:=N) T E V B C H v ∂ν)=
      ∫v,Z (Q) v/Z B v*chart v (fun U=>held V B U*H U) ∂ν := by
    apply integral_congr_ae;apply ae_of_all;intro v
    exact congrArg (fun t=>Z (Q) v/Z B v*t) (fiber v _ (eb.meas.mul eh.meas))
  have pos:0≤actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
    apply integral_nonneg;intro U
    apply mul_nonneg (actualConditionalDensity_nonneg R.family R.makes interior.le V U)
    by_cases h:U∈C
    · rw [Set.indicator_of_mem h];exact abs_nonneg _
    · rw [Set.indicator_of_notMem h]
  have estimate:=WilsonForestRetainedLaw.original R T E interior A S tails V C mc H eh
  dsimp only at estimate
  rw [←trueRow H eh inv,drawn,←trueRow _ eabs gabs] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_right paid pos)

end YM.Integration.WilsonForestRetainedIntegral
