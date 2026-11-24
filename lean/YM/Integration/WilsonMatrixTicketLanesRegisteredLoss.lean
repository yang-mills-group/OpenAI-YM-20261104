import YM.Integration.WilsonMatrixTicketLanesRegisteredNorm
import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy
import YM.Integration.PhysicalWilsonHotIntegral

/-! The actual mask error in a registered operator is negligible even after testing
against a polynomially priced earlier field and transporting to an earlier physical scale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredLoss
open Function Filter Set MeasureTheory Lattice RG Wilson MergeProof Source Push.Local
open RG12 RG17 OPE.Therm Extraction Spec IterationFour Push.AbsoluteSums.Animals
open Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesConnectedRegistered
open WilsonMatrixTicketLanesRegisteredNorm
open scoped Topology Classical BigOperators

variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:RG17.Layout F) {k N per d:ℕ}

private theorem measurable (live:k ≤ N) (v:R.family.label d) (o:Site (R.family.side k per)):
    Measurable (maskError R live v o):=by
  have h:Measurable (raw R live v o):=(R.family.localSection d).continuous_places _ o |>.measurable
  exact measurable_const.mul ((masked_measurable _ _ _ h).sub h)

private theorem retained (live:k ≤ N) (v:R.family.label d) (o:Site (R.family.side k per))
    (h:Config G (R.family.side k per)→ℂ):
    let X:=(R.family.localSection d).footprint o
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per k).p.threshold X
    E.indicator (fun U=>maskError R live v o U*h U)=fun U=>maskError R live v o U*h U:=by
  dsimp only []
  funext U
  by_cases bad:U∈SelectedCofactorAnchoredRegister.hot (R.family.path.rep N per k).p.threshold
      ((R.family.localSection d).footprint o)
  · exact Set.indicator_of_mem bad _
  · rw [Set.indicator_of_notMem bad]
    have good:RG.Healthy (R.family.path.rep N per k).p.threshold ((R.family.localSection d).footprint o) U:=
      Finset.disjoint_left.mpr fun a ax af=>bad ⟨a,ax,af⟩
    rw [clean R live v o U good,zero_mul]

include F L in
/-- There is no volume charge. Only the registered finite section at the actual placement
can trigger the rejection. The other field may use the entire configuration. -/
theorem tested (simple:G.Simple) (Y:Poetry R.family.path.levels) (d e b q:ℕ) {D C ε:ℝ}
    (hD:0 ≤ D) (hC:0 ≤ C) (hε:0<ε):
    ∀ᶠ k:ℕ in atTop,∀ N,(live:k ≤ N)→∀ per,(R.family.ref d ≤ k)→
      ∀ (v:R.family.label d) (o:Site (R.family.side k per)),
      mass R.family d (entry R d k N per v) ≤ D/(regulatorRun R.family N per k)^e→
      ∀ h:Config G (R.family.side k per)→ℂ,Measurable h→
      (∀U,‖h U‖ ≤ C/(regulatorRun R.family N per k)^b)→∀ j (earlier:j ≤ k),
      ∫ V,‖actualTransport R.family (N:=N) (p:=per)
        (fun U=>maskError R live v o U*h U) earlier V‖ ∂scene R.family.path N per j ≤ 
          ε*(regulatorRun R.family N per k)^q:=by
  let K:ℝ:=1+(2:ℝ)^d*stock R d
  have hK:0 ≤ K:=by dsimp [K,stock];positivity
  let cells:ℕ:=(R.family.localSection d).stencil.card*ballCost 2*Fintype.card PlaqAxes
  let tariff:=K*D*C
  have nonneg:0 ≤ tariff:=mul_nonneg (mul_nonneg hK hD) hC
  have full:=PhysicalWilsonHotIntegral.all_orders R simple Y (ρ:=1) zero_lt_one
    (C:=tariff*(cells:ℝ)) (mul_nonneg nonneg (Nat.cast_nonneg _)) hε q (d+e+b) 0
  filter_upwards [full,WilsonMatrixTicketLanesReportedAccuracy.small R simple 1 zero_lt_one]
    with k sale bounded N live per age v o invoice h hm fee j earlier
  let g:=regulatorRun R.family N per k
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  let X:=(R.family.localSection d).footprint o
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per k).p.threshold X
  let A:=fun U=>maskError R live v o U*h U
  have card:X.card*ballCost 2*Fintype.card PlaqAxes ≤ cells:=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Finset.card_image_le)
  have price:tariff/g^(d+e+b)*(X.card*ballCost 2*Fintype.card PlaqAxes:ℕ) ≤ 
      (tariff*(cells:ℝ))/g^(d+e+b):=by
    calc
      _ ≤ tariff/g^(d+e+b)*(cells:ℝ):=mul_le_mul_of_nonneg_left
        (by exact_mod_cast card) (div_nonneg nonneg (pow_nonneg gp.le _))
      _=_:=by ring
  have capped (U):‖A U‖ ≤ tariff/g^(d+e+b):=by
    rw [show A U=maskError R live v o U*h U from rfl,norm_mul]
    calc
      _ ≤ (K*(D/g^e)/g^d)*(C/g^b):=mul_le_mul
        ((loss R F L age live (bounded N per live) v o U).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left invoice hK) (pow_nonneg gp.le _)))
        (fee U) (norm_nonneg _) (div_nonneg (mul_nonneg hK (div_nonneg hD (pow_nonneg gp.le _))) (pow_nonneg gp.le _))
      _=_:=by dsimp [tariff];rw [pow_add,pow_add];field_simp [gp.ne']
  have raw:=sale N live per X E (SelectedCofactorAnchoredRegister.measurable _ _)
    (by simpa only [one_mul] using (Subset.rfl (s:=E)))
    0 le_rfl (tariff/g^(d+e+b)) (div_nonneg nonneg (pow_nonneg gp.le _)) price A
    ((measurable R live v o).mul hm) (fun U _=>capped U) j earlier
  have same:PhysicalWilsonHotIntegral.restricted (E:=E)
      ((Real.sqrt (R.family.path.levels.clock.forcedAllowance k))^0)⁻¹ A=A:=by
    unfold PhysicalWilsonHotIntegral.restricted
    simp only [pow_zero,inv_one,one_smul]
    exact retained R live v o h
  rw [same] at raw
  exact raw

/-- Convert the actual recorded thermal cap into the inverse coupling price required
above. It is uniform in the period and all subsequent ultraviolet cutoffs. -/
theorem cutoff (live:k ≤ N) (e:ℕ):
    (R.family.path.levels.clock.hatBeta k)^e ≤ (2:ℝ)^e/(regulatorRun R.family N per k)^(2*e):=by
  let g:=regulatorRun R.family N per k
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  apply (le_div_iff₀ (pow_pos gp _)).mpr
  rw [pow_mul,←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed k).le)
    (sq_nonneg _)) (WilsonMatrixTicketLanesReportedAccuracy.thermal R k N per live) e

end YM.Integration.WilsonMatrixTicketLanesRegisteredLoss
