import YM.Integration.WilsonDegreeFourInheritedPrimary

/-! The actual long regular rows of the earlier registered insertion under
the conditional law used by the degree-four pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonDegreeFourInheritedTail
open Function MeasureTheory Lattice RG Wilson Source Push.Local
open WilsonInheritedRegisteredField
open private real_test from YM.Integration.WilsonRegisteredDegreeFourCovariance
open scoped Classical
variable {G : Gauge} {C : Family G} (h : C.Makes) {k N per d : ℕ}

def tail (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per)) (b : ℕ)
    (U : Config G (C.side k per)) : ℂ :=
  let A := C.path.rep N per k
  let Z := packet h hk w o
  ∑' i, if b ≤ coverNumber A.p.B (Z.support i) then Z.maskedTerm A i U else 0

/-- The charge is the one already held by the same translated coefficient.
The exponential retains the native cover exponent at the actual date. -/
theorem field (hk : k ≤ N) (ref : C.ref d ≤ k) (w : C.label d)
    (o : Site (C.side k per)) (b : ℕ) (U : Config G (C.side k per)) :
    let A := C.path.rep N per k
    let Z := packet h hk w o
    ‖tail h hk w o b U‖ ≤ Real.exp (-A.p.supportExponent*(b:ℝ)) *
      ((C.path.levels.params k).columns*(C.labels.level d).coeffSize ((C.labels.level d).core Z.x)) := by
  intro A Z
  let e := Real.exp (-A.p.supportExponent*(b:ℝ))
  let f := fun i => if b ≤ coverNumber A.p.B (Z.support i) then Z.maskedTerm A i U else 0
  have paid := (WilsonTranslatedFactory.based h ref hk o ((C.factory d N per).terminal.symm w)).2
  obtain ⟨a,c,ha,hc,allFee,_,⟨p,P,S⟩,_⟩ := paid
  have point (i:ℕ) : ‖f i‖ ≤ e*A.p.mass (Z.support i) (p i) := by
    have spec:A.p.supBounds o (Z.support i) (Z.regular i) (p i):=S i
    by_cases high:b≤coverNumber A.p.B (Z.support i)
    · rw [show f i=Z.maskedTerm A i U from if_pos high]
      have observed : ‖Z.maskedTerm A i U‖ ≤ p i := by
        by_cases room:Healthy A.p.threshold (Z.support i) U
        · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ room]
          exact spec.2 U room [] (Nat.zero_le _) (by simp)
        · rw [Coefficient.maskedTerm,masked_ne _ _ _ _ room,norm_zero]
          exact spec.1
      have sep:A.p.supportExponent*(b:ℝ)≤A.p.supportExponent*((coverNumber A.p.B (Z.support i)):ℝ):=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr high) A.p.exponent_pos.le
      have gain : 1 ≤ e*Real.exp (A.p.supportExponent*(coverNumber A.p.B (Z.support i))) := by
        rw [show e=Real.exp (-A.p.supportExponent*(b:ℝ)) from rfl,←Real.exp_add]
        exact Real.one_le_exp (by linarith)
      apply observed.trans
      change _ ≤ e*(Real.exp _ * p i)
      rw [←mul_assoc]
      exact le_mul_of_one_le_left spec.1 gain
    · rw [show f i=0 from if_neg high,norm_zero]
      exact mul_nonneg (Real.exp_nonneg _) (P.1 i)
  have wallet:=sumBudget_mul_left P (Real.exp_nonneg (-A.p.supportExponent*(b:ℝ)))
  have bill : SumBudget (fun i=>‖f i‖) (e*a) :=
    sumBudget_mono wallet (fun i=>norm_nonneg _) point le_rfl
  exact ((norm_tsum_le_tsum_norm bill.2.1).trans bill.2.2).trans
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hc).trans allFee) (Real.exp_nonneg _))

open PhysicalNext.Repeat.Legato
variable (R:Run G) {j:ℕ}

/-- Every configuration of the old lower field and every cutoff share the
same signed first observation and the same lower partition. -/
theorem measured (hk : j+1 ≤ N) (ref : R.family.ref 4 ≤ j+1) (v w : R.family.label 4)
    (x : Site (R.family.side N per)) (o : Site (R.family.side (j+1) per))
    (η χ : ℂ →L[ℝ] ℝ) (V : Config G (R.family.side j per)) (b : ℕ) :
    let A := R.family.path.rep N per (j+1)
    let Z := packet (C:=R.family) R.makes hk w o
    let F := fun U=>η (actualTransport R.family (N:=N) (R.family.O N per v x) hk U)
    let E := actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
    let H := fun U=>F U-E F V
    let α := MergeProof.alto R.family.path (j+1) 4
    let fare := Real.exp (-A.p.supportExponent*(b:ℝ)) * ((R.family.path.levels.params (j+1)).columns*
      (R.family.labels.level 4).coeffSize ((R.family.labels.level 4).core Z.x))
    |E (fun U=>H U*χ (α*tail (C:=R.family) R.makes hk w o b U)) V| ≤
      ((‖χ‖*‖α‖)*fare)*E (fun U=>|H U|) V := by
  intro A Z F E H α fare
  let a := actualConditionalDensity R.family N per j V
  have past := WilsonMeasuredInheritedGauge.occupied R.family R.makes (per:=per) hk v x
  have eF : Envelope F := real_test past.1 η
  have held : Envelope H := by simpa only [H,sub_eq_add_neg] using eF.add (Envelope.const (-E F V))
  obtain ⟨u,upper,low⟩ := WilsonHeldExteriorLaw.upper_floor R N per j hk
  have weights:Envelope a:=(WilsonHeldExteriorLaw.regularity R N per j hk V A
    (A.envelope (R.makes.wilson.represents N per (j+1) hk).good) upper low).1
  let M:=((‖χ‖*‖α‖)*fare)
  let Q:=prior G (R.family.side (j+1) per)
  let lamps:=fun U=>χ (α*tail (C:=R.family) R.makes hk w o b U)
  have spec U : |lamps U|≤M := calc
    |lamps U| ≤ ‖χ‖*‖α*tail (C:=R.family) R.makes hk w o b U‖ := χ.le_opNorm _
    _ = (‖χ‖*‖α‖)*‖tail (C:=R.family) R.makes hk w o b U‖ := by rw [norm_mul,mul_assoc]
    _ ≤ M := mul_le_mul_of_nonneg_left (field R.makes hk ref w o b U) (by positivity)
  have absH : Envelope (fun U=>|H U|) := by
    obtain ⟨c,hc⟩:=held.cost
    exact ⟨held.meas.abs,c,fun U=>by simpa only [Real.norm_eq_abs,abs_abs] using hc U⟩
  have live : Integrable (fun U=>a U*|H U|) Q :=
    (weights.mul absH).integrable Q
  change |∫U,a U*(H U*lamps U) ∂Q|≤M*∫U,a U*|H U| ∂Q
  rw [←integral_const_mul]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (live.const_mul M)
  apply ae_of_all
  intro U
  have nonnegative : 0≤a U:=actualConditionalDensity_nonneg R.family R.makes hk V U
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg nonnegative]
  calc a U*(|H U| * |lamps U|) ≤ a U*(|H U| * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (spec U) (abs_nonneg _)) nonnegative
       _ = M*(a U*|H U|) := by ring

end YM.Integration.WilsonDegreeFourInheritedTail
