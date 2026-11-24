import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRegionalCoordinates

/-! A bounded gauge-invariant probe computed from the original field
in the physical box; the exterior can use it directly. The exact conversion
back to the true singleton preserves the local zero-mass or excessive-ratio
contribution against the original unmarked outside. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset Set MeasureTheory Lattice RG Wilson Marker Multi Extra.Histories Extra.Trajectories Comparison.RG02.Cumulants
  Primitives.GCC.Anchor QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def regionalProbe (L:Support n)(a:V)(t:T)(M:ℝ)(U:Config G n):ℂ:=
  let l:=leftField A L t U
  let s:=l.part (C.fire a)/l.part C.quiet
  if ‖s‖≤M then s else 0

omit [Fintype V] in
theorem bounded_regional_probe (L:Support n)(a:V)(t:T)(M:ℝ)(mp:0≤M):
    Measurable (regionalProbe A L a t M) ∧ UsesFinal P.p.threshold L (regionalProbe A L a t M) ∧
    (∀g U,regionalProbe A L a t M (gauge g U)=regionalProbe A L a t M U) ∧
    ∀U,‖regionalProbe A L a t M U‖≤M:=by
  obtain ⟨borel,localData,rot⟩:=left_field_local A L t
  let q:=fun U=>(leftField A L t U).part (C.fire a)/(leftField A L t U).part C.quiet
  have qm:Measurable q:=((Poly.part_cont _).measurable.comp borel).div ((Poly.part_cont _).measurable.comp borel)
  refine ⟨Measurable.ite (measurableSet_le qm.norm measurable_const) qm measurable_const,?_,?_,?_⟩
  · intro U W fine f
    unfold regionalProbe
    rw [localData U W fine f]
  · intro g U
    unfold regionalProbe
    rw [rot]
  intro U
  change ‖if ‖q U‖≤M then q U else 0‖≤M
  split
  · assumption
  simpa only [norm_zero] using mp

/-- Full signed conversion, with no lower bound on the truncated scalar.
The use of the same regional probe in both input terms is essential. -/
theorem original_regional_probe (L:Support n)(t:T)(U:Config G n)(live:0<P.eval U)
    (a:V)(inBox:o a∈L)(M:ℝ){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e):
    let ν:ℂ:=P.activities.gas P.p U
    let l:=leftField A L t U
    let r:=rightField A L t U
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    let q:=l.part (C.fire a)/l.part C.quiet
    let α:=regionalProbe A L a t M U
    let trueMean:=(A.gas t U).part (C.fire a)/ν
    ν*(trueMean-α)=E.part (C.fire a)-α*E.part C.quiet+
      (if l.part C.quiet=0 ∨ M<‖q‖ then l.part (C.fire a)*r.part C.quiet else 0):=by
  intro ν l r E q α trueMean
  have source:=actual_local_singleton A L t U live a inBox wp paid en
  change ν*(trueMean-q)=E.part (C.fire a)-q*E.part C.quiet+
      (if l.part C.quiet=0 then l.part (C.fire a)*r.part C.quiet else 0) at source
  have proxy:α=if ‖q‖≤M then q else 0:=rfl
  rw [proxy]
  by_cases ok:‖q‖≤M
  · simpa only [if_pos ok,not_lt_of_ge ok,or_false] using source
  rw [if_neg ok,if_pos (Or.inr (lt_of_not_ge ok)),sub_zero,zero_mul,sub_zero]
  have nz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  change ν*((A.gas t U).part (C.fire a)/ν)=_
  rw [mul_comm ν,div_mul_cancel₀ _ nz]
  let O:=univ.filter (fun v=>o v∈L)
  have ina:a∈O:=mem_filter.mpr ⟨mem_univ _,inBox⟩
  have fa:inside (C.fire a) O=C.fire a:=Subtype.ext (inter_eq_left.mpr (singleton_subset_iff.mpr ina))
  have za:diff (C.fire a) O=C.quiet:=Subtype.ext (sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr ina))
  have total:A.gas t U=remainingCash P.activities P.p U (A.K.hard t · U) L+E:=
    crossing_cash_exact P.activities P.p U _ L w wp (filed_actor_stock A wp paid en t U)
  have coord:(remainingCash P.activities P.p U (A.K.hard t · U) L).part (C.fire a)=l.part (inside (C.fire a) O)*r.part (diff (C.fire a) O):=
    regional_rows A L t U wp paid en (C.fire a)
  rw [total,Poly.part_plus,coord,fa,za,add_comm]

end YM.Integration.FVA1Physical.Exchange.RoseCut
