import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDeterminant
import YM.Extra.SOURCE_HISTORIES.Stock

/-! The left regional scalar and its marked field are measurable on the
actual local gauge and local failures: they can furnish a genuine local
numerical tester. Record exactly the missing event where its mass is zero.
No positivity or bounded inverse of the truncated physical mass is presumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset Set MeasureTheory Lattice RG Wilson Marker Multi Extra.Histories Extra.Trajectories Comparison.RG02.Cumulants
  Primitives.GCC.Anchor QuadraticLocal
open scoped Classical BigOperators
open private region_absent from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterConnected
open private retained_stock from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDebt

variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def leftField (L:Support n)(t:T)(U:Config G n):Poly C:=
  ∑'z:Pool (lies P.activities L),component P.activities (flags P.p.threshold U∩L) (A.K.hard t · U) z.val

def rightField (L:Support n)(t:T)(U:Config G n):Poly C:=
  ∑'z:Pool (fun i=>¬lies P.activities L i),component P.activities (flags P.p.threshold U\L)
    (retained P.activities L (A.K.hard t · U)) z.val

omit [Fintype V] in
theorem left_field_local (L:Support n)(t:T):
    Measurable (leftField A L t) ∧
    UsesFinal P.p.threshold L (leftField A L t) ∧
    ∀g U,leftField A L t (gauge g U)=leftField A L t U:=by
  have flagM:Measurable (fun U:Config G n=>flags P.p.threshold U):=by
    apply measurable_to_countable _
    intro K
    exact flags_measurable_eq ..
  refine ⟨?_,?_,?_⟩
  · apply Measurable.tsum
    intro z
    have event:MeasurableSet {U:Config G n|Regional P.activities (flags P.p.threshold U∩L) z.val}:=
      flagM ((Set.to_countable {F:Support n|Regional P.activities (F∩L) z.val}).measurableSet)
    exact Measurable.ite event (Finset.measurable_fun_prod _ fun i _=>(A.K.locality t i).borel) measurable_const
  · intro U W same flagsEq
    have feq:flags P.p.threshold U∩L=flags P.p.threshold W∩L:=by simpa only [inter_comm L] using flagsEq
    unfold leftField
    apply tsum_congr
    intro z
    unfold component
    rw [feq]
    split
    · exact prod_congr rfl (fun i hi=>(A.K.locality t i).reads U W
        (agrees_mono same (coe_subset.mpr (z.property i hi)))
        (Attach.narrow _ _ (z.property i hi) _ _ flagsEq))
    rfl
  intro g U
  unfold leftField
  apply tsum_congr
  intro z
  unfold component
  rw [gauge_flags]
  split
  · exact prod_congr rfl (fun i _=>(A.K.locality t i).gauge g U)
  rfl

theorem regional_rows (L:Support n)(t:T)(U:Config G n){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e):
    let O:=univ.filter (fun v=>o v∈L)
    ∀s:C.Mode,(remainingCash P.activities P.p U (A.K.hard t · U) L).part s=
      (leftField A L t U).part (inside s O)*(rightField A L t U).part (diff s O):=by
  intro O
  let B:=P.activities
  let p:=P.p
  let K:=fun i=>A.K.hard t i U
  have fund:=filed_actor_stock A wp paid en t U
  have carry (i:ℕ)(s:C.Mode)(h:(K i).part s≠0):∀v∈s.val,o v∈(B.forced i).support:=(A.K.locality t i).carry U s h
  let S:=retained B L K
  have stock:=retained_stock B L K w wp fund
  have inactive (i:ℕ)(nz:S i≠0)(out:¬lies B L i):Disjoint (B.forced i).support L:=by
    by_contra met
    exact nz (if_pos ⟨out,met⟩)
  have carries (i:ℕ)(s:C.Mode)(h:(S i).part s≠0):∀v∈s.val,o v∈(B.forced i).support:=by
    by_cases away:cross B L i
    · exact False.elim (h (by simp only [S,retained,if_pos away];rfl))
    exact carry i s (by simpa only [S,retained,if_neg away] using h)
  let l:=∑'z:Pool (lies B L),component B (flags p.threshold U∩L) S z.val
  let r:=∑'z:Pool (fun i=>¬lies B L i),component B (flags p.threshold U\L) S z.val
  have ls:l=withinSet O l:=by
    ext s
    rw [begin_inner_part]
    split
    · rfl
    next miss =>
      obtain ⟨v,seen,no⟩:=Finset.not_subset.mp miss
      apply region_absent B _ S _ w wp stock v _ s seen
      intro i isin f used
      by_contra nz
      exact no (mem_filter.mpr ⟨mem_univ _,isin (carries i f nz v used)⟩)
  have rs:r=without O r:=by
    ext s
    rw [begin_outer_part]
    split
    · rfl
    next miss =>
      obtain ⟨v,seen,located⟩:=not_disjoint_iff.mp miss
      apply region_absent B _ S _ w wp stock v _ s seen
      intro i outside f used
      by_contra nz
      have active:S i≠0:=by rintro h;exact nz (by rw [h];rfl)
      exact disjoint_left.mp (inactive i active outside) (carries i f nz v used) (mem_filter.mp located).2
  have actual:l=leftField A L t U:=by
    apply tsum_congr
    intro z
    unfold component
    split
    · apply prod_congr rfl
      intro i hi
      exact if_neg (fun h=>h.1 (z.property i hi))
    rfl
  intro s
  change (remainingCash B p U K L).part s=(leftField A L t U).part (inside s O)*r.part (diff s O)
  rw [←actual]
  have exactLeft:remainingCash B p U K L=l*r:=original_full_cut B p U S L inactive w wp stock
  rw [exactLeft]
  calc (l*r).part s=(withinSet O l*without O r).part s:=congrArg (fun A:Poly C=>A.part s) (congrArg₂ (·*·) ls rs)
       _=l.part (inside s O)*r.part (diff s O):=part_split O l r s


/-- An exact, local reference for the genuine single-source mean. Its
entire residual is either a signed crossed-actor row or the true surviving
zero-regional-mass correction. The exterior scalar has not been detached. -/
theorem actual_local_singleton (L:Support n)(t:T)(U:Config G n)(live:0<P.eval U)
    (a:V)(inBox:o a∈L){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e):
    let ν:ℂ:=P.activities.gas P.p U
    let l:=leftField A L t U
    let r:=rightField A L t U
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    let localMean:=l.part (C.fire a)/l.part C.quiet
    let trueMean:=(A.gas t U).part (C.fire a)/ν
    ν*(trueMean-localMean)=E.part (C.fire a)-localMean*E.part C.quiet+
      (if l.part C.quiet=0 then l.part (C.fire a)*r.part C.quiet else 0):=by
  intro ν l r E localMean trueMean
  let O:=univ.filter (fun v=>o v∈L)
  have ina:a∈O:=mem_filter.mpr ⟨mem_univ _,inBox⟩
  have fq:inside C.quiet O=C.quiet:=Subtype.ext (empty_inter O)
  have zq:diff C.quiet O=C.quiet:=Subtype.ext (empty_sdiff O)
  have fa:inside (C.fire a) O=C.fire a:=Subtype.ext (inter_eq_left.mpr (singleton_subset_iff.mpr ina))
  have za:diff (C.fire a) O=C.quiet:=Subtype.ext (sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr ina))
  have total:A.gas t U=remainingCash P.activities P.p U (A.K.hard t · U) L+E:=
    crossing_cash_exact P.activities P.p U _ L w wp (filed_actor_stock A wp paid en t U)
  have rows:=regional_rows A L t U wp paid en
  have coord:∀h:C.Mode,(A.gas t U).part h=l.part (inside h O)*r.part (diff h O)+E.part h:=by
    intro h
    rw [total,Poly.part_plus,rows]
  have actual:=coord (C.fire a)
  have quiet:=coord C.quiet
  have base:(A.gas t U).part C.quiet=ν:=Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t U)
  rw [base,fq,zq] at quiet
  rw [fa,za] at actual
  have nz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  dsimp only [trueMean,localMean]
  rw [mul_sub,mul_comm ν (_/ν),div_mul_cancel₀ _ nz,actual,quiet]
  by_cases zero:l.part C.quiet=0
  · simp [zero,add_comm]
  rw [if_neg zero]
  field_simp [zero]
  ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
