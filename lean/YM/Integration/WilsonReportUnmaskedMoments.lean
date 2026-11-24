import YM.Integration.WilsonReportWindowCalendar

/-! Every disconnected moment of the actual deposited window has the same
all-order integral as its fitted section plus the retained signed regular
rows. All intermediate products are bounded on the real rough configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportUnmaskedMoments
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Vitrines Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonReportWindowSource WilsonReportWindowEnvelope
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G}

private theorem point {n : ℕ} (I : Finset (Fin n)) (x y : Fin n→ℂ) {M : ℝ}
    (h1 : 1≤M) (hx : ∀ j,‖x j‖≤M) (hy : ∀ j,‖y j‖≤M) :
    ‖(∏j∈I,x j)-(∏j∈I,y j)‖ ≤ M^I.card*∑j∈I, ‖x j-y j‖ := by
  have m0 := zero_le_one.trans h1
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I gone ih =>
    let X := ∏i∈I,x i
    let Y := ∏i∈I,y i
    let S := ∑i∈I,‖x i-y i‖
    have yB : ‖Y‖≤M^I.card := by
      dsimp only [Y]; rw [norm_prod]
      exact (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>hy i)).trans_eq (by simp)
    simp only [prod_insert gone,sum_insert gone,card_insert_of_notMem gone,pow_succ]
    change ‖x j*X-y j*Y‖≤M^I.card*M*(‖x j-y j‖+S)
    calc
      _ = ‖x j*(X-Y)+(x j-y j)*Y‖ := congrArg norm (by ring)
      _ ≤ ‖x j‖*‖X-Y‖+‖x j-y j‖*‖Y‖ := by
        simpa only [norm_mul] using norm_add_le (x j*(X-Y)) ((x j-y j)*Y)
      _ ≤ M*(M^I.card*S)+‖x j-y j‖*M^I.card := add_le_add
        (mul_le_mul (hx j) ih (norm_nonneg _) m0) (mul_le_mul_of_nonneg_left yB (norm_nonneg _))
      _ ≤ _ := by nlinarith only [le_mul_of_one_le_right (mul_nonneg (norm_nonneg (x j-y j)) (pow_nonneg m0 I.card)) h1]

private theorem integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} (I : Finset (Fin n)) (F S : Fin n→Ω→ℂ) {M e : ℝ}
    (h1 : 1≤M) (e0 : 0≤e) (EF : ∀ j,Envelope (F j)) (ES : ∀ j,Envelope (S j))
    (hF : ∀ j U,‖F j U‖≤M) (hS : ∀ j U,‖S j U‖≤M)
    (localBill : ∀ j,(∫U,‖F j U-S j U‖ ∂μ)≤e) :
    ‖(∫U,∏j∈I,F j U ∂μ)-∫U,∏j∈I,S j U ∂μ‖≤ M^n*((n:ℝ)*e) := by
  have af := (Envelope.prodC I F (fun j _=>EF j)).integrableC μ
  have as' := (Envelope.prodC I S (fun j _=>ES j)).integrableC μ
  have orig (j : Fin n) : Integrable (fun U=>‖F j U-S j U‖) μ :=
    (((EF j).integrableC μ).sub ((ES j).integrableC μ)).norm
  have count : I.card≤n := (Finset.card_le_univ I).trans_eq (Fintype.card_fin _)
  have sum := integrable_finsetSum I (fun j _=>orig j)
  rw [←integral_sub af as']
  calc
    _ ≤ ∫U,‖(∏j∈I,F j U)-(∏j∈I,S j U)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫U,M^I.card*∑j∈I,‖F j U-S j U‖ ∂μ := integral_mono (af.sub as').norm (sum.const_mul _) (fun U=>
      point I (fun j=>F j U) (fun j=>S j U) h1 (fun j=>hF j U) (fun j=>hS j U))
    _ = M^I.card*∑j∈I,(∫U,‖F j U-S j U‖ ∂μ) := by rw [integral_const_mul, integral_finsetSum I (fun j _=>orig j)]
    _ ≤ M^I.card*∑ _j∈I,e := mul_le_mul_of_nonneg_left (sum_le_sum (fun j _=>localBill j))
      (pow_nonneg (zero_le_one.trans h1) _)
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul (pow_le_pow_right₀ h1 count) (mul_le_mul_of_nonneg_right (by exact_mod_cast count) e0)
        (mul_nonneg (Nat.cast_nonneg _) e0) (pow_nonneg (zero_le_one.trans h1) _)

private theorem cancel {M A g e : ℝ} (P n q : ℕ) (gp : 0<g) :
    (M*A/g^P)^n*((n:ℝ)*(e*A*g^(q+P*n)))=((n:ℝ)*e*M^n)*A^(n+1)*g^q := by
  rw [div_pow,mul_pow,pow_add,←pow_mul,pow_succ]
  field_simp

/-- All original finite apertures and all their signed subset products. The
single physical temperature threshold precedes every regulator, period, list
of submitted labels and set of translated positions. -/
theorem physical (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    {n : ℕ} (d : Fin n→ℕ) (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ N p : ℕ,k<N → ∀ (v : (j:Fin n)→R.family.label (d j))
      (x : Fin n→Site (R.family.side k p)) (I : Finset (Fin n)),
    let C := R.family; let B := (C.path.levels.budget k).B; let μ := Therm.scene C.path N p k
    ‖(∫U,∏j∈I,bead C (d j) k N p B (v j) (x j) U ∂μ)-
      ∫U,∏j∈I,opened C (N:=N) (v j) (x j) U ∂μ‖ ≤
      ε*(1+∑j,Spindle.paid C (d j) k N p (v j))^(n+1)*(regulatorRun C N p k)^q := by
  obtain ⟨P,M,m1,calendar⟩ := WilsonReportWindowCalendar.original hG W funding subsidy d
  have m0 := zero_le_one.trans m1
  let c := (n:ℝ)*M^n
  let e := ε/(1+c)
  have c0 : 0≤c := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg m0 _)
  have den : 0<1+c := by linarith only [c0]
  have ep : 0<e := div_pos hε den
  have fee : (n:ℝ)*e*M^n ≤ ε := by
    have back := div_mul_cancel₀ ε den.ne'
    change e*(1+c)=ε at back
    dsimp only [c] at back
    nlinarith only [back,ep]
  have alarms := eventually_all.mpr fun j : Fin n=>WilsonReportWindowAlarm.physical hG W funding subsidy (d j) (q+P*n) ep
  have grades := eventually_all.mpr fun j : Fin n=>(eventually_ge_atTop (R.family.ref (d j)))
  filter_upwards [calendar,alarms,grades,eventually_gt_atTop (R.family.ref 0)] with k cal bank grade zero N p cut v x I
  let C := R.family
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability R.makes.wilson cut.le
  let g := regulatorRun C N p k
  let B := (C.path.levels.budget k).B
  let A := 1+∑j,Spindle.paid C (d j) k N p (v j)
  let H := M*A/g^P
  let F (j : Fin n) := bead C (d j) k N p B (v j) (x j)
  let S (j : Fin n) := opened C (N:=N) (v j) (x j)
  obtain ⟨gp,g1,_,unitsPaid⟩ := cal N p cut.le
  have gp' : 0<g := gp
  have paid0 (j : Fin n) := Spindle.paid_pos C (d j) k N p (v j)
  have A1 : 1≤A := le_add_of_nonneg_right (sum_nonneg (fun j _=>paid0 j))
  have A0 := zero_le_one.trans A1
  have price (j : Fin n) : Spindle.paid C (d j) k N p (v j)≤A :=
    (single_le_sum (f:=fun j=>Spindle.paid C (d j) k N p (v j)) (fun i _=>paid0 i) (mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  have H₁ : 1≤H := (le_div_iff₀ (pow_pos gp' _)).mpr (by
    rw [one_mul]; exact (pow_le_one₀ gp'.le g1).trans (one_le_mul_of_one_le_of_one_le m1 A1))
  have rows (j : Fin n) := regulated hG W funding subsidy (v j) (grade j) zero cut (x j)
  have budgets (j : Fin n) : units C (d j) k N p*Spindle.paid C (d j) k N p (v j)≤H := by
    apply (le_div_iff₀ (pow_pos gp' _)).mpr
    rw [mul_right_comm]
    exact mul_le_mul (unitsPaid j) (price j) (paid0 j) m0
  have localBill (j : Fin n) : (∫U,‖F j U-S j U‖ ∂μ) ≤ e*A*g^(q+P*n) := by
    have eqv : (F j)-(S j)=alarm C (N:=N) (v j) (x j) := (rows j).2.2.2.1
    have value (U) : F j U-S j U=alarm C (N:=N) (v j) (x j) U := congrFun eqv U
    simp_rw [value]
    exact (bank j N cut.le p (v j) (x j)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (price j) ep.le) (pow_nonneg gp'.le _))
  have e0 : 0≤e*A*g^(q+P*n) := mul_nonneg (mul_nonneg ep.le A0) (pow_nonneg gp'.le _)
  have bound := integral μ I F S H₁ e0 (fun j=>(rows j).1) (fun j=>(rows j).2.1)
    (fun j U=>((rows j).2.2.2.2 U).1.trans (budgets j))
    (fun j U=>((rows j).2.2.2.2 U).2.trans (budgets j)) localBill
  exact bound.trans ((cancel (M:=M) (A:=A) (e:=e) P n q gp').le.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right fee (pow_nonneg A0 _)) (pow_nonneg gp'.le _)))

end YM.Integration.WilsonReportUnmaskedMoments
end

