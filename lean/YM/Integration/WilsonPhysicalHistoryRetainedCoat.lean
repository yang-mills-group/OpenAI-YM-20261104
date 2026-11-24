import YM.Integration.WilsonPhysicalHistoryRetainedActivity
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Depot

/-! The original numbered old action, its retained Spring, and its single
omitted insertion on the same affine fluctuation of the actual coat. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson Pressure Pressure.Tube Tree
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Bloch Laurent Push Push.AbsoluteSums Precision Exterior Shell Channel
open PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} {c f : Side}

private theorem regular_split (P : BudgetPoint) (A K D : Activities G f)
    (hk : K.reg=A.reg) (hd : D.reg=A.reg) (fields : A.E=K.E+D.E)
    (i : ℕ) (U : Config G f) :
    A.regularOccurrence P i U = K.regularOccurrence P i U+D.regularOccurrence P i U := by
  have e := congrFun (congrFun fields i) U
  unfold Activities.regularOccurrence
  rw [hk,hd]
  by_cases h : Healthy P.threshold (A.reg i).support U
  · simp only [masked_eq _ _ _ _ h]
    exact e
  · simp only [masked_ne _ _ _ _ h,add_zero]

private theorem regular_bound (P : BudgetPoint) (E : Activities G f) {i : ℕ} {b : ℝ}
    (h : P.supBounds (E.reg i).site (E.reg i).support (E.E i) b) (U : Config G f) :
    |E.regularOccurrence P i U|≤b := by
  by_cases live : Healthy P.threshold (E.reg i).support U
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ live,←Real.norm_eq_abs]
    exact h.2 U live [] (Nat.zero_le _) (by simp)
  · rw [Activities.regularOccurrence,masked_ne _ _ _ _ live,abs_zero]
    exact h.1

section coat
variable {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

private theorem original_head (X : Coat T F) (P : Rep G f) (K D : Activities G f)
    (hk : K.reg=P.activities.reg) (hd : D.reg=P.activities.reg)
    (fields : P.activities.E=K.E+D.E) (a : ℝ) (u : Directions G f) (i : ℕ) :
    X.inhale P a u (.inl i)-X.inhale { P with activities:=K } a u (.inl i) =
      -D.regularOccurrence P.p i (X.input u)*
        X.enforce (2*a) u (X.plaza (Raw.regularFoot S.ratio 0 X.B P i)) := by
  change -P.activities.regularOccurrence P.p i (X.input u)*
      X.enforce (2*a) u (X.plaza (Raw.regularFoot S.ratio 0 X.B P i)) -
    (-K.regularOccurrence P.p i (X.input u)*
      X.enforce (2*a) u (X.plaza (Raw.regularFoot S.ratio 0 X.B {P with activities:=K} i))) = _
  simp only [Raw.regularFoot,hk]
  rw [regular_split P.p P.activities K D hk hd fields i (X.input u)]
  ring

private theorem original_forced (X : Coat T F) (P : Rep G f) (K : Activities G f)
    (hf : K.forced=P.activities.forced) (hc : K.K=P.activities.K) (a : ℝ) (u : Directions G f) (i : ℕ) :
    X.bag { P with activities:=K } a u i = X.bag P a u i := by
  simp [Coat.bag,Raw.forcedFoot,hf,hc]

end coat

variable (R : Run G) {N n j : ℕ} (hj : j<N)

set_option pp.explicit true in
theorem coat_rows {d : ℕ} (A : Comparison R (p:=n) hj d) :
    let P := R.family.path.rep N n j
    let Q := approximation R (p:=n) hj d
    let E := remainder R (p:=n) hj d
    ∃ b : ℕ→ℝ,
      (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
         P.p.mass (P.activities.reg i).support (b i) else 0)
        ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1))) ∧
      ∀ {c : Side} {S : StepData c (R.family.side j n)} {T : Tube G S}
        {F : Forest S.ratio} (X : Coat T F) (a : ℝ) (C : ChartRatio G)
        (z : Air (R.family.side j n) G) (i : ℕ),
        let u:=X.liftA P.beta z
        let L:=X.farLog P a C z (.inl (.inl i))-X.farLog Q a C z (.inl (.inl i))
        L= -E.regularOccurrence P.p i (X.input u)*
          X.enforce (2*a) u (X.plaza (Raw.regularFoot S.ratio 0 X.B P i)) ∧
        |L|≤b i ∧ X.bag P a u i=X.bag Q a u i := by
  dsimp only
  let P:=R.family.path.rep N n j
  let Q:=approximation R (p:=n) hj d
  let E:=remainder R (p:=n) hj d
  obtain ⟨representation,hk,hd,fields,hf,hc,b,cap,root⟩:=retained_rows R hj A
  use b
  refine ⟨?_,?_⟩
  · intro x
    convert root x using 1
    ext i
    by_cases h : ((R.family.path.rep N n j).activities.reg i).site=x
    · simp [hd,h]
      rfl
    · simp [hd,h]
      intro eq
      exact (h eq).elim
  · intro c S T F X a C z i
    let u:=X.liftA P.beta z
    have same : Q.beta=P.beta := A.coupling
    have row : X.farLog P a C z (.inl (.inl i))-X.farLog Q a C z (.inl (.inl i)) =
        -E.regularOccurrence P.p i (X.input u)*X.enforce (2*a) u
          (X.plaza (Raw.regularFoot S.ratio 0 X.B P i)) := by
      change X.inhale P a u (.inl i)-X.inhale Q a (X.liftA Q.beta z) (.inl i)=_
      rw [same]
      exact (congrArg (fun Q' : Rep G _=>X.inhale P a u (.inl i)-X.inhale Q' a u (.inl i))
        representation).trans (original_head X P Q.activities E hk hd fields a u i)
    refine ⟨row,?_,?_⟩
    · rw [row,abs_mul,abs_neg]
      have force:=X.conserve (X.plaza (Raw.regularFoot S.ratio 0 X.B P i)) (2*a) u
      rw [abs_of_nonneg force.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) force.2).trans
        (regular_bound P.p E (cap i) (X.input u))
    · exact ((congrArg (fun Q' : Rep G _=>X.bag Q' a u i) representation).trans
        (original_forced X P Q.activities hf hc a u i)).symm

end YM.Integration.OriginalMarkedRunAction
