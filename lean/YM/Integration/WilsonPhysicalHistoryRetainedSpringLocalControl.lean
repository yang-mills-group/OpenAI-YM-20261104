import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalTilt
import YM.Integration.SignedWeightedMoment

/-! The two genuine local laws have unit quiet component even on large
supports. Saturating their bounded readings removes the exponential in the local fee. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OriginalMarkedRowCovariance
open scoped Classical BigOperators
variable {G:Gauge}

private theorem read_controls {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    {k:X→ℝ}(e:Envelope k)(pos:∀u,0<k u):
    read μ k 1=1 ∧ ∀(F:X→ℂ)(B:ℝ),(∀u,‖F u‖≤B)→‖read μ k F‖≤B:=by
  have mass:0<∫u,k u ∂μ:=by
    apply (integral_pos_iff_support_of_nonneg (fun u=>(pos u).le) (e.integrable μ)).2
    rw [show Function.support k=Set.univ from Set.eq_univ_of_forall fun u=>(pos u).ne'];simp
  let ν:=SignedWeightedMoment.normalized μ k
  letI:IsProbabilityMeasure ν:=SignedWeightedMoment.mass_one μ e (fun u=>(pos u).le) mass
  have moved (F:X→ℂ):read μ k F=∫u,F u ∂ν:=by
    simpa only [OriginalMarkedRowCovariance.read,Complex.real_smul,Complex.ofReal_inv]
      using (SignedWeightedMoment.normalized_integral μ e.meas (fun u=>(pos u).le) mass F).symm
  constructor
  · rw [moved];simp
  · intro F B cap
    rw [moved]
    simpa using norm_integral_le_of_norm_le (integrable_const (μ:=ν) B) (Filter.Eventually.of_forall cap)

theorem spring_control (R:Run G){N per j:ℕ}(live:j≤N)(r:ℕ)(Z:SeriesA G)(σ C:ℝ)
    {X:Type*}[MeasurableSpace X][Nonempty X](μ:Measure X)[IsProbabilityMeasure μ]
    (ξ:X → Config G (R.family.side j per))(mx:Measurable ξ)(exterior:Config G (R.family.side j per))
    (borel:Measurable (maskedSpringScore R N per j r Z σ C))(a:ℝ)
    (bound:∀u,|maskedSpringScore R N per j r Z σ C (ξ u)-maskedSpringScore R N per j r Z σ C exterior|≤a):
    let E:=read μ (fun u=>(R.family.path.rep N per j).eval (ξ u))
    let L:=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u))
    E 1=1 ∧ L 1=1 ∧ ∀(F:X→ℂ)(B:ℝ),(∀u,‖F u‖≤B)→
      ‖E F‖≤B ∧ ‖L F‖≤B ∧ (Measurable F→‖L F-E F‖≤2*Real.exp 2*a*B):=by
  intro E L
  let d:=maskedSpringScore R N per j r Z σ C
  let y (u:X):=(R.family.path.rep N per j).eval (ξ u)
  let z (u:X):=Real.exp (d (ξ u))
  have p (u:X):0<y u:=Multi.AxisShift.chosen_positive R.makes.wilson live (ξ u)
  have shown:=RG02.Actual.eval_envelope R.makes.wilson (p:=per) live
  obtain ⟨M,cap⟩:=shown.cost
  have ep:Envelope y:=⟨shown.meas.comp mx,M,fun u=>cap _⟩
  have eh:Envelope z:=⟨Real.measurable_exp.comp (borel.comp mx),Real.exp (a+d exterior),fun u=>by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (sub_le_iff_le_add.mp (abs_le.mp (bound u)).2)⟩
  have actual:(fun u:X=>maskedSpringWeight R (N:=N) r Z σ C (ξ u))=z*y:=funext fun u=>spring_tilt R r Z σ C _
  have left:=read_controls μ ep p
  have right:=read_controls μ (eh.mul ep) (fun u=>mul_pos (Real.exp_pos _) (p u))
  have exact_l:L=read μ (z*y):=congrArg (fun k=>read μ k) actual
  refine ⟨left.1,by rw [exact_l];exact right.1,?_⟩
  intro F B cap
  have l:‖L F‖≤B:=by rw [exact_l];exact right.2 F B cap
  have e:‖E F‖≤B:=left.2 F B cap
  refine ⟨e,l,?_⟩
  intro meas
  have b:0≤B:=(norm_nonneg _).trans (cap (Classical.choice (inferInstance:Nonempty X)))
  have ha:0≤a:=(abs_nonneg _).trans (bound (Classical.choice (inferInstance:Nonempty X)))
  by_cases small:a≤1
  · have h:=spring_fiber R live r Z σ C μ ξ mx exterior borel a bound F meas B b cap
    have le:Real.exp (2*a)≤Real.exp 2:=Real.exp_le_exp.mpr (by linarith)
    exact h.trans (by gcongr)
  · have cash:1≤Real.exp 2*a:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) (le_of_not_ge small)
    calc ‖L F-E F‖≤‖L F‖+‖E F‖:=norm_sub_le _ _
         _≤B+B:=add_le_add l e
         _≤2*Real.exp 2*a*B:=by nlinarith only [mul_le_mul_of_nonneg_right cash b]

end YM.Integration.OriginalMarkedRunAction
