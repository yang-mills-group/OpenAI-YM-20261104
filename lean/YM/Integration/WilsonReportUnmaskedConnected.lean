import YM.Integration.WilsonReportUnmaskedMoments
import YM.Integration.WilsonReportMomentDifference

/-! The complete cumulant after removing the true primary alarm. Its retained
regular rows and every disconnected partner remain on the original Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportUnmaskedConnected
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Vitrines Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonReportWindowSource WilsonReportWindowEnvelope
open Primitives.GCC.Anchor Comparison.RG02.Cumulants WilsonReportMomentDifference
open Extra.Trajectories (connected)
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G}

private theorem product_gap {I : Type*} [DecidableEq I] (q : Finset I) (f g : I → ℂ)
    {e M : ℝ} (he : 0 ≤ e) (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ M)
    (h : ∀ i, ‖f i-g i‖ ≤ e) : ‖(∏ j ∈ q, f j) - (∏ j ∈ q, g j)‖ ≤ q.card*e*M^q.card := by
  induction q using Finset.induction_on with
  | empty => simp
  | @insert i q hi ih =>
    let X := ∏ j ∈ q, f j
    let Y := ∏ j ∈ q, g j
    have hy : ‖Y‖ ≤ M^q.card := by
      dsimp only [Y]
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hg j)).trans_eq (by simp)
    simp only [prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    change ‖f i*X-g i*Y‖ ≤ ((q.card:ℝ)+1)*e*(M^q.card*M)
    calc
      _ = ‖f i*(X-Y)+(f i-g i)*Y‖ := congrArg norm (by ring)
      _ ≤ ‖f i‖*‖X-Y‖+‖f i-g i‖*‖Y‖ := by simpa only [norm_mul] using norm_add_le (f i*(X-Y)) ((f i-g i)*Y)
      _ ≤ M*(q.card*e*M^q.card)+e*M^q.card := add_le_add
        (mul_le_mul (hf i) ih (norm_nonneg _) (zero_le_one.trans hM))
        (mul_le_mul (h i) hy (norm_nonneg _) he)
      _ ≤ _ := by nlinarith only [le_mul_of_one_le_right (mul_nonneg he (pow_nonneg (zero_le_one.trans hM) q.card)) hM]

private theorem joined {c e M A g : ℝ} (P n h q : ℕ) (gp : 0<g) :
    c*(e*A^(n+1)*g^(q+P*h))*(M*A/g^P)^h=c*e*M^h*A^(n+1+h)*g^q := by
  rw [div_pow,mul_pow,←pow_mul,pow_add g,pow_add A]
  field_simp
  ring

private theorem combine {n : ℕ} (Γ : Census (Fin n)) (C : Family G) {k N p : ℕ}
    (law : C.Makes) (cut : k≤N) (F L : Fin n→ Config G (C.side k p)→ℂ) {M e : ℝ}
    (h1 : 1≤M) (e0 : 0≤e) (hF : ∀j U,‖F j U‖≤M) (hL : ∀j U,‖L j U‖≤M)
    (admitted : ∀ I : Finset (Fin n),‖(∫U,∏j∈I,F j U ∂(Therm.scene C.path N p k))-
      ∫U,∏j∈I,L j U ∂(Therm.scene C.path N p k)‖≤e) (s : Γ.Mode) :
    ‖(connected (reported Γ C (N:=N) F)).part s-(connected (reported Γ C (N:=N) L)).part s‖ ≤
      WilsonReportMomentDifference.multiplicity Γ s*e*M^(n*Fintype.card (Hot Γ)) := by
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability law.wilson cut
  let A := reported Γ C (N:=N) F
  let B := reported Γ C (N:=N) L
  have au : A.part Γ.quiet=1 := by change (∫ U,∏j∈(∅:Finset (Fin n)),F j U ∂μ)=1; simp
  have bu : B.part Γ.quiet=1 := by change (∫ U,∏j∈(∅:Finset (Fin n)),L j U ∂μ)=1; simp
  have bound (K : Fin n→ Config G (C.side k p)→ℂ) (hk : ∀j U,‖K j U‖≤M) (u : Γ.Mode) :
      ‖(reported Γ C (N:=N) K).part u‖≤M^n := by
    have point (U : Config G (C.side k p)) : ‖∏j∈u.val,K j U‖≤M^n := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _j∈u.val,M := Finset.prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>hk j U)
        _ = M^u.val.card := by simp
        _ ≤ M^n := pow_le_pow_right₀ h1 ((Finset.card_le_univ u.val).trans_eq (Fintype.card_fin _))
    exact (norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall point)).trans_eq (by rw [probReal_univ,mul_one])
  change ‖(connected A).part s-(connected B).part s‖≤_
  rw [log_partition A au, log_partition B bu, ←Finset.sum_sub_distrib,WilsonReportMomentDifference.multiplicity,Finset.sum_mul,Finset.sum_mul]
  refine (norm_sum_le ..).trans (sum_le_sum (fun t _=>?_))
  rw [←mul_sub,norm_mul]
  have phase := product_gap t.val (fun i : Hot Γ=>A.part i.val) (fun i : Hot Γ=>B.part i.val)
    e0 (one_le_pow₀ (n:=n) h1) (fun i=>bound F hF i.val) (fun i=>bound L hL i.val)
    (fun i=>admitted i.val.val)
  have wide := (pow_le_pow_right₀ (one_le_pow₀ (n:=n) h1) (Finset.card_le_univ t.val)).trans_eq (pow_mul ..).symm
  exact (mul_le_mul_of_nonneg_left (phase.trans (mul_le_mul_of_nonneg_left wide
    (mul_nonneg (Nat.cast_nonneg _) e0))) (norm_nonneg _)).trans_eq (by ring)

/-- Independent running source labels and grading; no independence of the
actual heat events, windows or different branches of the correlation is used. -/
theorem physical (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ N p : ℕ,k<N → ∀ (v : (j:Fin n)→R.family.label (d j))
      (x : Fin n→Site (R.family.side k p)) (s : Γ.Mode),
    let C := R.family; let B := (C.path.levels.budget k).B
    let F (j : Fin n) := bead C (d j) k N p B (v j) (x j)
    let S (j : Fin n) := opened C (N:=N) (v j) (x j)
    ‖(connected (reported Γ C (N:=N) F)).part s-(connected (reported Γ C (N:=N) S)).part s‖ ≤
      ε*(1+∑j,Spindle.paid C (d j) k N p (v j))^(n+1+n*Fintype.card (Hot Γ))*(regulatorRun C N p k)^q := by
  obtain ⟨P,M,m1,calendar⟩ := WilsonReportWindowCalendar.original hG W funding subsidy d
  let h := n*Fintype.card (Hot Γ)
  let c := 1+∑s:Γ.Mode,WilsonReportMomentDifference.multiplicity Γ s
  have mult (s : Γ.Mode) : 0≤ WilsonReportMomentDifference.multiplicity Γ s := sum_nonneg (fun t _=>mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have denom : 1≤c := le_add_of_nonneg_right (sum_nonneg (fun t _=>mult t))
  have cpos := zero_lt_one.trans_le denom
  have mp := zero_lt_one.trans_le m1
  let e := ε/(c*M^h)
  have den := mul_pos cpos (pow_pos mp h)
  have ep : 0<e := div_pos hε den
  have total : c*e*M^h=ε := by
    rw [mul_comm c e,mul_assoc]; exact div_mul_cancel₀ ε den.ne'
  have invoices := WilsonReportUnmaskedMoments.physical hG W funding subsidy d (q+P*h) ep
  have grades := eventually_all.mpr fun j : Fin n=>eventually_ge_atTop (R.family.ref (d j))
  filter_upwards [calendar,invoices,grades,eventually_gt_atTop (R.family.ref 0)] with k cal invoice grade zero N p cut v x s
  let C := R.family
  let g := regulatorRun C N p k
  let B := (C.path.levels.budget k).B
  let A := 1+∑j,Spindle.paid C (d j) k N p (v j)
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
  have H₁ : 1≤M*A/g^P := (le_div_iff₀ (pow_pos gp' _)).mpr (by
    rw [one_mul]; exact (pow_le_one₀ gp'.le g1).trans (one_le_mul_of_one_le_of_one_le m1 A1))
  have rows (j : Fin n) := regulated hG W funding subsidy (v j) (grade j) zero cut (x j)
  have budgets (j : Fin n) : units C (d j) k N p*Spindle.paid C (d j) k N p (v j)≤M*A/g^P := by
    apply (le_div_iff₀ (pow_pos gp' _)).mpr
    rw [mul_right_comm]
    exact mul_le_mul (unitsPaid j) (price j) (paid0 j) mp.le
  let E := e*A^(n+1)*g^(q+P*h)
  have E0 : 0≤E := mul_nonneg (mul_nonneg ep.le (pow_nonneg A0 _)) (pow_nonneg gp'.le _)
  have paid := combine Γ C R.makes cut.le F S H₁ E0
    (fun j U=>((rows j).2.2.2.2 U).1.trans (budgets j))
    (fun j U=>((rows j).2.2.2.2 U).2.trans (budgets j))
    (fun I=>invoice N p cut v x I) s
  have coff : WilsonReportMomentDifference.multiplicity Γ s≤c := (single_le_sum (f:=WilsonReportMomentDifference.multiplicity Γ) (fun i _=>mult i) (mem_univ s)).trans
    (le_add_of_nonneg_left zero_le_one)
  apply paid.trans
  calc
    _ ≤ c*E*(M*A/g^P)^h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coff E0)
      (pow_nonneg (zero_le_one.trans H₁) _)
    _ = _ := (joined (c:=c) (e:=e) (M:=M) (A:=A) P n h q gp').trans (by rw [total])

end YM.Integration.WilsonReportUnmaskedConnected
end

