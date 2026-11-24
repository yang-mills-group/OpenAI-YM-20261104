import YM.Integration.WilsonMatrixTicketLanesConnectedRegistered
import YM.Integration.WilsonMatrixTicketLanesRegulatorColumn
import YM.Integration.WilsonRegisteredWindowRestriction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredNorm
open Lattice RG Next.Rank OPE RG12 Extraction Spec Wilson Pert.Asymptotics
open PhysicalNext.Repeat.Legato RGComparison.Core16 Spool RG16.Literal
open Next.Rank.Price MergeProof Source RG17 RGComparison.Core16.Astage Push.Local WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesConnectedRegistered
open WilsonMatrixTicketLanesReportedPivot WilsonInheritedRegisteredField
open scoped BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:RG17.Layout F)

/-- The compact bound uses only the fixed registered sections in this engineering grade. -/
def stock (d:ℕ):ℝ:=1+∑ j,|WilsonRegisteredWindowRestriction.wordBound
  (fun _:Unit=>WilsonCoherentTerminalFrame.lamp R d j)|

private theorem stock_pos (d:ℕ):0<stock R d:=by unfold stock;positivity

private theorem light (d:ℕ) (j:(R.family.labels.level d).Index) {n:Side} (o:Site n) (U:Config G n):
    ‖Light (WilsonCoherentTerminalFrame.lamp R d j) n o U‖  ≤  stock R d:=by
  let K:=fun j=>(WilsonRegisteredWindowRestriction.wordBound (fun _:Unit=>WilsonCoherentTerminalFrame.lamp R d j))
  have h:‖Light (WilsonCoherentTerminalFrame.lamp R d j) n o U‖ ≤ K j:=by
    simpa only [K,Spool.tally,Fintype.prod_unique] using (WilsonRegisteredWindowRestriction.word
      (fun _:Unit=>WilsonCoherentTerminalFrame.lamp R d j) (fun _:Unit=>o) U)
  unfold stock
  exact h.trans ((le_abs_self _).trans ((Finset.single_le_sum
    (f:=fun j=>|K j|) (fun i _=>abs_nonneg _) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)))

variable {k N per d:ℕ}

private theorem scale (future:k ≤ N) (small:regulatorRun R.family N per k ≤ 1)
    (i:(R.family.labels.level d).Index):
    (regulatorRun R.family N per k)^d*(R.family.path.levels.clock.threshold k)⁻¹^((R.family.labels.level d).grades i).2 ≤ (2:ℝ)^d:=by
  let g:=regulatorRun R.family N per k
  let t:=R.family.path.levels.clock.threshold k
  let ν:=((R.family.labels.level d).grades i).2
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson future))
  have tp:0<t:=(R.family.path.levels.budget k).threshold_pos
  have depth:ν ≤ d:=Planned.PrimaryIntegral295.Film.second_fits (R.family.labels.level d) i
  calc
    g^d*t⁻¹^ν ≤ g^ν*t⁻¹^ν:=mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one gp.le small depth) (pow_nonneg (inv_nonneg.mpr tp.le) _)
    _=(shrink R.family k N per)^ν:=by change _=(g/t)^ν;rw [div_eq_mul_inv,mul_pow]
    _ ≤ (2:ℝ)^ν:=pow_le_pow_left₀ (shrink_pos R.family R.makes future per).le
      (RG12.Arche.shrink_current (C:=R.family) (p:=per) R.makes future) _
    _ ≤ (2:ℝ)^d:=pow_le_pow_right₀ one_le_two depth

include F L in
/-- Uniform on the complete compact configuration space and the upper regulators. The price
is the true registered cutoff charge with one inverse coupling for each possible Taylor leg. -/
theorem operator_norm (age:R.family.ref d ≤ k) (future:k ≤ N)
    (small:regulatorRun R.family N per k ≤ 1) (v:R.family.label d)
    (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    ‖R.family.O k per (center R k N per v) o U‖ ≤ 
      ((2:ℝ)^d*stock R d)*mass R.family d (entry R d k N per v)/(regulatorRun R.family N per k)^d:=by
  let g:=regulatorRun R.family N per k
  let t:=R.family.path.levels.clock.threshold k
  let x:=entry R d k N per v
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson future))
  have tp:0<t:=(R.family.path.levels.budget k).threshold_pos
  apply (le_div_iff₀ (pow_pos gp d)).mpr
  rw [mul_comm,physical R F L d k N per age future v o U]
  calc
    _ ≤ g^d*∑ i,‖(R.family.labels.level d).scaled t⁻¹ x i*
        Light (WilsonCoherentTerminalFrame.lamp R d i) (R.family.side k per) o U‖:=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg gp.le _)
    _=∑ i,(g^d*t⁻¹^((R.family.labels.level d).grades i).2)*
        ‖Light (WilsonCoherentTerminalFrame.lamp R d i) (R.family.side k per) o U‖*‖x i‖:=by
      rw [Finset.mul_sum];refine Finset.sum_congr rfl fun i _=>?_
      rw [norm_mul,Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr tp.le) _)];ring
    _ ≤ ∑ i,((2:ℝ)^d*stock R d)*‖x i‖:=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
      (mul_le_mul (scale R future small i) (light R d i o U) (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _=_:=by rw [←Finset.mul_sum];rfl

/-- Only the nonlinear part is excised. The vacuum coefficient is the literal zeroth
coordinate of the same price-scaled transferred enrollment. -/
theorem unit_norm (live:k ≤ N) (v:R.family.label d) (o:Site (R.family.side k per)):
    ‖alto R.family.path k d*(packet (C:=R.family) R.makes live v o).x 0‖ ≤ 
      mass R.family d (entry R d k N per v):=by
  have coord: (packet (C:=R.family) R.makes live v o).x =
      ((R.family.factory d N per).entries k ((R.family.factory d N per).terminal.symm v)).x:=
    WilsonTranslatedFactory.coordinate R.makes live o _
  rw [coord]
  change ‖(_ :ℂ)*_‖ ≤ _
  have eq:(alto R.family.path k d)*
      ((R.family.factory d N per).entries k ((R.family.factory d N per).terminal.symm v)).x 0=
      (entry R d k N per v) 0:=by simp only [WilsonMatrixTicketLanesRegulatorColumn.entry,alto,Pi.smul_apply,smul_eq_mul,Complex.ofReal_pow]
  rw [eq]
  exact (norm_le_pi_norm _ _).trans (RG12.norm_le_mass R.family d _)

include F L in
/-- The cost is zero on every healthy local field. Elsewhere the finite compact field bound
holds without any assumption on the remainder of the torus. -/
theorem loss (age:R.family.ref d ≤ k) (live:k ≤ N) (small:regulatorRun R.family N per k ≤ 1)
    (v:R.family.label d) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    ‖maskError R live v o U‖ ≤  (1+(2:ℝ)^d*stock R d)*
      mass R.family d (entry R d k N per v)/(regulatorRun R.family N per k)^d:=by
  let g:=regulatorRun R.family N per k
  let x:=entry R d k N per v
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have mx:0 ≤ mass R.family d x:=RG12.mass_nonneg _ _ _
  by_cases health:RG.Healthy (R.family.path.rep N per k).p.threshold ((R.family.localSection d).footprint o) U
  · rw [clean R live v o U health,norm_zero]
    exact div_nonneg (mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity) (stock_pos R d).le)) mx) (pow_nonneg gp.le _)
  · have diff:maskError R live v o U=alto R.family.path k d*(packet (C:=R.family) R.makes live v o).x 0-
          R.family.O k per (center R k N per v) o U:=by
      rw [unmasked R live v o U];unfold maskError;dsimp only [];rw [masked_ne _ _ _ _ health];ring
    rw [diff]
    calc
      _  ≤  _:=norm_sub_le _ _
      _  ≤  mass R.family d x+((2:ℝ)^d*stock R d)*mass R.family d x/g^d:=
        add_le_add (unit_norm R live v o) (operator_norm R F L age live small v o U)
      _  ≤  mass R.family d x/g^d+((2:ℝ)^d*stock R d)*mass R.family d x/g^d:=by
        exact add_le_add ((le_div_iff₀ (pow_pos gp _)).mpr
          (mul_le_of_le_one_right mx (pow_le_one₀ gp.le small))) le_rfl
      _ = _:=by ring

end YM.Integration.WilsonMatrixTicketLanesRegisteredNorm
