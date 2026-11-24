import YM.Integration.WilsonPositionSeparatedProfileReportingCut

/-! Total variation of a signed insertion stopped at a fixed reporting date
and then passed through the genuine translated Wilson child averages. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileReportingVariation
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open OPE.Therm RG05Readout Address Native Harvest RG05Readout.Records MergeProof Accent
open WilsonPositionSeparatedProfileReportingCut
open scoped Classical BigOperators Topology
variable {G : Gauge}

private theorem push {c f : Side} (S : StepData c f) {β : ℝ} (h : S.IsKernel β G)
    (X : Config G f→ℂ) (live : Integrable X (prior G _)) :
    (∫V,‖S.push β X V‖ ∂prior G c)≤∫U,‖X U‖ ∂prior G f := by
  rw [←StepData.push_integral h _ live.norm]
  apply integral_mono (StepData.push_integrable h X live).norm (StepData.push_integrable h _ live.norm)
  intro V
  change ‖∫U,S.density β U V • X U ∂prior G f‖≤∫U,S.density β U V • ‖X U‖ ∂prior G f
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp only [norm_smul,Real.norm_of_nonneg (h.positive _ _),smul_eq_mul]

variable (C : Family G) (law : C.Makes) (N per : ℕ)

private theorem high {h v : ℕ} (date : v≤h) (X : Config G (C.side h per)→ℂ)
    (live : Integrable X (prior G _)) :
    (∫U,‖gust C.path N per h X v date U‖ ∂prior G _)≤∫W,‖X W‖ ∂prior G _ := by
  induction date using Nat.decreasingInduction with
  | self => rw [gust_base]
  | of_succ i hi ih =>
    rw [gust_step _ _ _ _ X hi]
    exact (push _ (C.path.levels.transition_mass ..) _ (gust_live C.path N per h X live hi)).trans ih

private theorem branch {k : ℕ} (F : Bin G (C.side (k+1) per)) (live : BLight F)
    {δ : ℝ} (price : ∀g,(∫U,‖F g U‖ ∂prior G _)≤δ) (g : Body) :
    (∫V,‖journey C per k N 0 F g V‖ ∂prior G _)≤δ := by
  let I:=Bud C per k
  let Z (i : I):=sailS C k per F g i
  let S:=C.path.levels.clock.op k per
  let β:=C.path.β N per (k+1)
  let J (i : I):=S.push β (Z i)
  have fund (i : I):Integrable (Z i) (prior G _):=sail_lit F live g i
  have actual (i : I):Integrable (J i) (prior G _):=StepData.push_integrable (C.path.levels.transition_mass ..) _ (fund i)
  have bill (i : I) : (∫V,‖J i V‖ ∂prior G _)≤δ := by
    refine (push S (C.path.levels.transition_mass ..) (Z i) (fund i)).trans ?_
    exact ((prior_pull (G:=G) (1:Signed) (child C per k i)).integral_comp
      (WardBin.Wheels.embedding_pull _ _) (fun V=>‖F (Many.headFee C per k i g) V‖)).le.trans (price _)
  unfold journey Address.average blast
  simp only [pow_zero,one_smul,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,norm_mul,norm_inv,Complex.norm_natCast,integral_const_mul]
  change (Fintype.card I:ℝ)⁻¹*(∫V,‖∑i:I,J i V‖ ∂prior G _)≤δ
  have cap:(∫V,‖∑i:I,J i V‖ ∂prior G _)≤∫V,∑i:I,‖J i V‖ ∂prior G _ := by
    apply integral_mono (integrable_finsetSum _ (fun i _=>actual i)).norm
      (integrable_finsetSum _ (fun i _=>(actual i).norm))
    exact fun V => norm_sum_le _ _
  rw [integral_finsetSum _ (fun i _=>(actual i).norm)] at cap
  have nz : 0<(Fintype.card I:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  refine (mul_le_mul_of_nonneg_left (cap.trans (Finset.sum_le_sum (fun i _=>bill i))) (inv_pos.mpr nz).le).trans_eq ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ nz.ne',one_mul]

private theorem descent {n u : ℕ} (span : u≤n) (F : Bin G (C.side (n+1) per)) (live : BLight F)
    {δ : ℝ} (price : ∀g,(∫U,‖F g U‖ ∂prior G _)≤δ) :
    BLight (lower C N per n F u span) ∧ ∀g,(∫V,‖lower C N per n F u span g V‖ ∂prior G _)≤δ := by
  induction span using Nat.decreasingInduction with
  | self =>
    rw [show lower C N per n F n le_rfl=journey C per n N 0 F from Nat.decreasingInduction_self ..]
    exact ⟨sailed F live,branch C N per F live price⟩
  | of_succ i hi ih =>
    rw [show lower C N per n F i hi.le=journey C per i N 0 (lower C N per n F (i+1) hi)
      from Nat.decreasingInduction_succ_left ..]
    exact ⟨sailed _ ih.1,branch C N per _ ih.1 ih.2⟩

include law in
theorem original {h n u : ℕ} (issued : h≤N) (date : n+1≤h) (span : u≤n)
    (X : Goods G (C.side h per))
    (live : Integrable (fun V=>(C.path.rep N per h).eval V • X V) (prior G _)) (g : Body) :
    (∫V,‖field C N per date span X g V‖ ∂scene C.path N per u)≤∫V,‖X V‖ ∂scene C.path N per h := by
  let Q:=stock C N per date X
  have lit : BLight Q:= fun _=>gust_live C.path N per h _ live date
  have receipt:= (descent C N per span Q lit (fun _=>high C N per date _ live)).2 g
  have reach:=span.trans ((Nat.le_succ n).trans (date.trans issued))
  have normalized (V : Config G (C.side u per)) : (C.path.rep N per u).eval V • ‖field C N per date span X g V‖=
      ‖lower C N per n Q u span g V‖ := by
    have pos:=Multi.AxisShift.chosen_positive law.wilson reach V
    change (C.path.rep N per u).eval V * ‖lower C N per n Q u span g V/((C.path.rep N per u).eval V:ℂ)‖=_
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg pos.le,mul_div_cancel₀ _ pos.ne']
  rw [actualScene_formula C law reach,actualScene_formula C law issued]
  simp_rw [normalized]
  have top (V : Config G (C.side h per)):‖(C.path.rep N per h).eval V • X V‖=(C.path.rep N per h).eval V • ‖X V‖ := by
    rw [norm_smul,Real.norm_of_nonneg (Multi.AxisShift.chosen_positive law.wilson issued V).le,smul_eq_mul]
  simp_rw [top] at receipt
  exact mul_le_mul_of_nonneg_left receipt (inv_pos.mpr (Wilson.partition_pos ..)).le

end YM.Integration.WilsonPositionSeparatedProfileReportingVariation
