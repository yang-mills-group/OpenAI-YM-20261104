import YM.Integration.ManuscriptQLocalRawMaskCalendar

/-! Direct consumers on the original analytic packet input, before the final force and vacuum comparisons. -/

set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPreparedConditional
open PhysicalNext.Repeat.Legato LocalComparison
open Finset Lattice RG RG.Shoot Wilson Marker MeasureTheory Comparison.RG02
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open ManuscriptQLocalPacketGrades ManuscriptQLocalOriginalConditionalTail
open ManuscriptQLocalRegularConditional Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)

def cell (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (U : Config G n) (i : ℕ) : Poly Γ :=
  match P.packet i with
  | none=>0
  | some T=>Poly.send (P.mode i) (masked p.threshold T.plot (fun v=>P.term (testInclusion D x) g v i) U)

omit [Fintype V] in
theorem total (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (U : Config G n) :
    source P p g x 1 U=∑'i,cell P p g x U i := by
  rw [ManuscriptQLocalOriginalConditionalTail.physical]
  calc _ = ∑'i : Live P,cell P p g x U i := by
         exact tsum_congr fun i=>by simp only [cell,chosen P i,field]
       _ = _ := by
         apply tsum_subtype_eq_of_support_subset
         intro i hi
         cases h : P.packet i with
         | none=>exact (hi (by simp [cell,h])).elim
         | some T=>change (P.packet i).isSome;simp [h]

omit [Fintype V] in
theorem phase_cell (p : BudgetPoint) {g : ℝ} (hg : g≠0) (ξ : ℂ) (x : IndependentTests D)
    (U : Config G n) (i : ℕ) : cell (phaseSource P g ξ) p g x U i=
      ξ^(P.power i).toNat • cell P p g x U i := by
  let c := ξ^(P.power i).toNat*(effective P).coefficient g i
  cases h : P.packet i with
  | none=>simp [cell,phaseSource,Grading.amplified,h]
  | some T=>
    have h' : (phaseSource P g ξ).packet i=some (scaleToken c T) := by
      simp [phaseSource,Grading.amplified,h,c]
    simp only [cell,h',h]
    change Poly.send (P.mode i) (masked p.threshold T.plot (fun v=>(phaseSource P g ξ).term (testInclusion D x) g v i) U)=_
    by_cases hu : Healthy p.threshold T.plot U
    · rw [masked_eq _ _ _ _ hu,masked_eq _ _ _ _ hu,phase_term,(effective P).term hg]
      ext t
      by_cases ht : t=P.mode i <;> simp [Poly.part_send,Poly.part_smul,ht]
    · simp [masked_ne _ _ _ _ hu]

omit [Fintype V] in
/-- The full original measured field, including every test and independent
support mask, is unchanged by removal of positive powers at phase one. -/
theorem physical (p : BudgetPoint) {g : ℝ} (hg : g≠0) (x : IndependentTests D) (U : Config G n) :
    source (phaseSource P g 1) p g x 1 U=source P p g x 1 U := by
  rw [total,total]
  exact tsum_congr fun i=>by simp only [phase_cell P p hg,one_pow,one_smul]

variable (R : Run G) (d : LocalFormal.Datum R.family Γ) {J : Request V} {A : NumericSchedule R.family J}
    (F : AnalyticInput J A d)
local notation "nf" => R.family.side (d.level+1) d.period
local notation "nc" => R.family.side d.level d.period
local notation "gf" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "B₀" => (R.family.path.rep d.cutoff d.period (d.level+1)).p
local notation "w" => (fun v=>F.inputRadii v/F.kernelCosts v)

/- The original F supplies all pre-g debit at each independent phase.
Numerical capacity, width, test radii and geometric inputs are the actual
ones from the request. The geometry hypotheses are the original fine
tariff's support and threshold comparisons. -/
end YM.Integration.ManuscriptQLocalPreparedConditional
end

/-! Physical curvature endpoint prices on every regular marked source, with its original measured conditional law and no differentiated support charge. -/

set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPhysicalConditional
open PhysicalNext.Repeat.Legato LocalComparison
open Function Finset Lattice RG RG.Shoot Wilson Marker MeasureTheory Comparison.RG02
open Progress.DirectedRecipe LocalComparison Comparison.Density.RenderM Comparison.Density.RenderM.Token
open Push.Local Push.AbsoluteSums FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
    {q : BudgetPoint} {L : V→Support n} {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {width budget : ℝ} {off slope : ℕ} (H : P.Paid q L region w 1 width budget off slope)

def charge (θ g : ℝ) (i : Live P) := ‖(g:ℂ)^P.power i‖*θ^(P.rank i)*(token P i).coin

omit [Fintype V] in
include H in
/-- Every tested curvature face is based at an actual point of the declared
packet support. A mask on that support bounds each original curvature value. -/
theorem cold (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (i : Live P) :
    0≤charge P p.threshold g i ∧ ∀u,‖field P p g x i u‖≤charge P p.threshold g i := by
  let T := token P i
  let z := testInclusion D x
  have hc := H.coefficient i T (chosen P i)
  have hpos : 0≤charge P p.threshold g i := mul_nonneg
    (mul_nonneg (norm_nonneg _) (pow_nonneg p.threshold_pos.le _)) hc.1
  refine ⟨hpos,fun u=>?_⟩
  by_cases h : Healthy p.threshold T.plot u
  · have each (j : Fin (P.rank i)) :
        G.chord (faceValue u (WilsonCurvatureEndpoints.face (T.path j) T.root))≤p.threshold := by
      let S := T.path j
      have hp : S.offset∈S.stencil := Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_cons_self))
      have hq : wrap n S.offset+T.root∈(T.re z).footprint T.root := Finset.mem_image.mpr
        ⟨_,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hp⟩),rfl⟩
      by_contra! bad
      exact Finset.disjoint_left.mp h ((H.paths i T (chosen P i) z).2 hq)
        ((flags_spec ..).mpr ⟨_,List.mem_toFinset.mpr (List.mem_cons_self),bad⟩)
    have val := WilsonCurvatureEndpoints.cold T z (hc.2 x) p.threshold p.threshold_pos.le u each
    rw [field,masked_eq _ _ _ _ h]
    simp only [MarkedPackets.term,chosen P i,norm_mul]
    simpa only [charge,mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left val (norm_nonneg ((g:ℂ)^P.power i))
  · rw [field,masked_ne _ _ _ _ h,norm_zero]
    exact hpos

/-- The Laurent and curvature powers cancel on the radius 1/g before any
root sum is taken. -/
theorem cancellation {a : ℤ} {k : ℕ} (he : 0≤a+(k:ℤ)) {g θ X : ℝ} (hg : 0<g)
    (hθ : 0≤θ) (hX : θ≤X*g) : (g⁻¹)^(a+(k:ℤ)).toNat*‖(g:ℂ)^a‖*θ^k ≤ X^k := by
  have hz : ((a+(k:ℤ)).toNat:ℤ)=a+(k:ℤ) := Int.toNat_of_nonneg he
  have hbase : (g⁻¹)^(a+(k:ℤ)).toNat*g^a*g^k=1 := by
    rw [inv_pow,←zpow_natCast g (a+(k:ℤ)).toNat,←zpow_neg,←zpow_natCast g k,
      ←zpow_add₀ hg.ne',←zpow_add₀ hg.ne',hz]
    convert zpow_zero g using 1
    ring
  rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hg.le]
  calc _ ≤ (g⁻¹)^(a+(k:ℤ)).toNat*g^a*(X*g)^k := mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ hθ hX k) (mul_nonneg (pow_nonneg (inv_nonneg.mpr hg.le) _) (zpow_nonneg hg.le a))
       _ = ((g⁻¹)^(a+(k:ℤ)).toNat*g^a*g^k)*X^k := by rw [mul_pow];ring
       _ = _ := by rw [hbase,one_mul]

include H in
/-- Native original roots at coupling one pay the entire countable physical
source at the largest regular radius. All true support choices remain in the
source field. Only the norm of the value is used at this stage. -/
theorem reserve (θ g X : ℝ) (hθ : 0≤θ) (hg : 0<g) (hr : θ≤X*g) (hX : 1≤X) :
    SumBudget (ManuscriptQLocalCountableConditional.charge (fun i : Live P=>P.mode i) (slot P) w
      (charge P θ g) g⁻¹) (Fintype.card V*(X^P.rankCap*budget)) := by
  let f := ManuscriptQLocalCountableConditional.charge (fun i : Live P=>P.mode i) (slot P) w (charge P θ g) g⁻¹
  let raw (v : V) (i : ℕ) := if v∈(P.mode i).val then match P.packet i with
    | none=>0
    | some T=>Poly.toll w (P.mode i)*‖(1:ℂ)^P.power i‖*T.coin*Real.exp (width*T.fall) else 0
  have hrank : 0≤X^P.rankCap := pow_nonneg (zero_le_one.trans hX) _
  have hc (i : Live P) := (H.coefficient i (token P i) (chosen P i)).1
  have hf (i : Live P) : 0≤f i := mul_nonneg
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hg.le) _) (Poly.worth H.positive _).le)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hθ _)) (hc i))
  have each (i : Live P) (v : V) (hv : v∈(P.mode i).val) : f i≤X^P.rankCap*raw v i := by
    have hpow := cancellation (P.nonnegative_grade i (token P i) (chosen P i)) hg hθ hr
    have hc' := hpow.trans (pow_le_pow_right₀ hX (P.rank_bounded i (token P i) (chosen P i)))
    have cap := mul_le_mul_of_nonneg_right hc' (mul_nonneg (Poly.worth H.positive (P.mode i)).le (hc i))
    have he : 1≤Real.exp (width*((token P i).fall:ℝ)) := Real.one_le_exp
      (mul_nonneg H.width_pos.le (Nat.cast_nonneg _))
    simp only [raw,if_pos hv,chosen P i,one_zpow,norm_one,mul_one]
    refine le_trans (b:=X^P.rankCap*(Poly.toll w (P.mode i)*(token P i).coin)) ?_
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (mul_nonneg (Poly.worth H.positive (P.mode i)).le (hc i)) he) hrank)
    simpa only [f,ManuscriptQLocalCountableConditional.charge,charge,slot,engineering,
      mul_comm,mul_left_comm,mul_assoc] using cap
  have localRoot (v : V) : SumBudget (fun i : Live P=>if v∈(P.mode i).val then f i else 0) (X^P.rankCap*budget) := by
    refine budget_of_sum (fun i=>by split <;> simp [hf]) (fun e=>?_)
    calc _ ≤ ∑i∈e,X^P.rankCap*raw v i.val := by
           refine Finset.sum_le_sum fun i _=>?_ 
           by_cases hv : v∈(P.mode i).val
           · simpa only [if_pos hv] using each i v hv
           · simp [hv,raw]
         _ = X^P.rankCap*(∑i∈e.image Subtype.val,raw v i) := by
           rw [Finset.mul_sum,Finset.sum_image (fun i _ j _ h=>Subtype.ext h)]
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_left _ hrank
           refine le_trans (Finset.sum_le_sum (fun i hi=>?_)) (budget_sum (H.roots v) (e.image Subtype.val))
           cases h:P.packet i <;> by_cases hv:v∈(P.mode i).val <;> simp [raw,h,hv]
  have all := rooted_sumBudget hf (fun i : Live P=>Finset.nonempty_iff_ne_empty.mpr
    (fun h=>(hot P i) (Subtype.ext h))) localRoot
  simpa [nsmul_eq_mul] using all

section Measured
variable (R : Run G) (d : LocalFormal.Datum R.family Γ) {J : Request V} {A : NumericSchedule R.family J}
local notation "nf" => R.family.side (d.level+1) d.period
local notation "nc" => R.family.side d.level d.period
local notation "B₀" => (R.family.path.rep d.cutoff d.period (d.level+1)).p
local notation "gf" => regulatorRun R.family d.cutoff d.period (d.level+1)

omit [Fintype V] in
theorem threshold (A : NumericSchedule R.family J) :
    (B₀).threshold≤A.admittedCost d.level*gf := by
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have same:(B₀)=R.family.path.levels.budget (d.level+1):=(R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).vac
  rw [same]
  apply (div_le_iff₀ hg).1
  have h := A.cost_covers_units d.level d.cutoff d.period d.below
  have h0 : 0≤R.family.path.levels.clock.threshold d.level/gf :=
    div_nonneg (R.family.path.levels.budget d.level).threshold_pos.le hg.le
  exact (le_add_of_nonneg_left h0).trans h

/-- Every original analytic input at every independent phase contributes
its entire masked regular source. The only scale condition is the true
small physical coupling. All thresholds, prices and tree degrees are
read off the given run, request, packet family and analytic input. -/
theorem bare (F : AnalyticInput J A d) (P₀ : MarkedPackets J.tests G nf Γ)
    (paid₀ : P₀.Paid (A.inputNorm d.level) F.inputAddresses F.inputRegion
      (fun v=>F.inputRadii v/F.kernelCosts v) 1 (A.inputWidth d.level) (A.admittedCost d.level) F.coverOffset F.coverSlope) (weak : gf≤1)
    (x : IndependentTests J.tests) (U : Config G nc) (s : Γ.Mode) (k : ℕ) :
    let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
    let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ B₀ gf x) z)
    ∃ p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
      Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
        (ℓ+1:ℕ)*(gf^(k+1)*connectedBill Γ (Fintype.card V*((A.admittedCost d.level)^P₀.rankCap*A.admittedCost d.level))) := by
  let mode := fun i : Live P₀=>P₀.mode i
  let f := field P₀ B₀ gf x
  let funds := charge P₀ (B₀).threshold gf
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have pay := reserve P₀ paid₀ (B₀).threshold gf (A.admittedCost d.level) (B₀).threshold_pos.le hg
    (threshold R d A) (A.admitted_cost_ge_one _)
  have hfee : ∀i,0≤funds i := fun i=>(cold P₀ paid₀ B₀ gf x i).1
  have hrow : ∀i u,‖f i u‖≤funds i := fun i=>(cold P₀ paid₀ B₀ gf x i).2
  have raised : 1≤gf⁻¹ := (one_le_inv₀ hg).2 weak
  have hdeg := ManuscriptQLocalCountableConditional.degree mode (slot P₀) f paid₀.positive hfee hrow raised pay (hot P₀)
  have hwhole := ManuscriptQLocalCountableConditional.whole mode (slot P₀) f paid₀.positive hfee hrow raised pay
  have hquiet := ManuscriptQLocalCountableConditional.quiet mode (slot P₀) f paid₀.positive hfee hrow raised pay (hot P₀)
  have meas := ManuscriptQLocalCountableConditional.measured mode (slot P₀) f (ManuscriptQLocalOriginalConditionalTail.measured P₀ paid₀ B₀ gf x)
  apply ManuscriptQLocalConditionalGradeTail.conditional R.family R.makes d.below U (source P₀ B₀ gf x)
    (fun _:V=>P₀.powerCap+P₀.rankCap) hdeg paid₀.positive _ (fun z u=>(hwhole z u).2) _ hquiet hg weak _ s k
  · intro z t
    exact ((Poly.get t).continuous.measurable.comp (Poly.pass_cont.measurable.comp (meas z))).aestronglyMeasurable
  · exact ManuscriptQLocalCountableConditional.capped mode (slot P₀) f paid₀.positive hrow raised pay

theorem unit_phase (F : AnalyticInput J A d) (weak : gf≤1) (ξ : ℂ) (hξ : ‖ξ‖=1)
    (x : IndependentTests J.tests) (U : Config G nc) (s : Γ.Mode) (k : ℕ) :
    let P₀ := ManuscriptQLocalPacketGrades.phaseSource F.packets gf ξ
    let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
    let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ B₀ gf x) z)
    ∃ p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
      Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
        (ℓ+1:ℕ)*(gf^(k+1)*connectedBill Γ (Fintype.card V*((A.admittedCost d.level)^P₀.rankCap*A.admittedCost d.level))) := by
  exact bare R d F _ (ManuscriptQLocalPacketGrades.phase_earned F.packets F.input_paid
    (IterationFour.Currency.g_pos R.makes _ _ _ d.below) weak ξ hξ) weak x U s k

end Measured
end YM.Integration.ManuscriptQLocalPhysicalConditional
end

/-! One cutoff for the genuine measured regular-source tail, chosen before the input packet family or period. -/

set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalRegularCalendar
open PhysicalNext.Repeat.Legato LocalComparison
open Filter Finset Lattice RG RG.Shoot Wilson Marker Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ManuscriptQLocalRegularConditional ManuscriptQLocalOriginalConditionalTail Pert.Asymptotics
open scoped Classical BigOperators Topology

theorem absorb {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (K r : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N p : ℕ, m < N →
      let g := Pert.Asymptotics.regulatorRun C N p (m+1)
      0<g → g≤1 → A.admittedCost m^K*g^r≤g^((r:ℝ)-η) := by
  let e := η/(K+1:ℝ)
  obtain ⟨start,h⟩ := A.cost_subpower e (div_pos hη (by positivity))
  refine ⟨start,fun m hm N p hN hg h1=>?_⟩
  let g := Pert.Asymptotics.regulatorRun C N p (m+1)
  have ha := pow_le_pow_left₀ (A.admitted_cost_nonnegative m) (h m hm N p hN) K
  have price : e*(K:ℝ)≤η := by
    have h0 : 0<(K+1:ℝ) := by positivity
    have heq : e*(K+1:ℝ)=η := by unfold e;field_simp
    have he : 0≤e := (div_pos hη h0).le
    linarith only [heq,he]
  calc
    _ ≤ (g^(-e))^K*g^r := mul_le_mul_of_nonneg_right ha (pow_nonneg hg.le _)
    _ = g^((-e)*(K:ℝ)+(r:ℝ)) := by
      rw [←Real.rpow_natCast (g^(-e)) K,←Real.rpow_mul hg.le,←Real.rpow_natCast g r,←Real.rpow_add hg]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hg h1 (by linarith)


theorem exp_pos (n : ℕ) {b : ℝ} (hb : 0≤b) : 0≤expBill n b :=
  Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (pow_nonneg hb _)
theorem log_pos (n : ℕ) {b : ℝ} (hb : 0≤b) : 0≤logBill n b :=
  Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith) _)
theorem exp_mono (n : ℕ) {a b : ℝ} (ha : 0≤a) (h : a≤b) : expBill n a≤expBill n b :=
  Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h i) (norm_nonneg _)
theorem log_mono (n : ℕ) {a b : ℝ} (ha : 0≤a) (h : a≤b) : logBill n a≤logBill n b :=
  Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (show a+1≤b+1 by linarith) (i+1)) (norm_nonneg _)

theorem exp_scale (n : ℕ) {a x : ℝ} (ha : 0≤a) (hx : 1≤x) :
    expBill n (a*x)≤x^n*expBill n a := by
  unfold expBill
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj=>?_
  rw [mul_pow]
  have h := pow_le_pow_right₀ hx (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  simpa only [mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg ((j.factorial:ℂ)⁻¹)) (pow_nonneg ha _))

theorem log_scale (n : ℕ) {a x : ℝ} (ha : 0≤a) (hx : 1≤x) :
    logBill n (a*x)≤x^n*logBill n a := by
  unfold logBill
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj=>?_
  have hbase : a*x+1≤(a+1)*x := by linarith
  have hnon : 0≤a*x+1 := by positivity
  have hpow := pow_le_pow_left₀ hnon hbase (j+1)
  rw [mul_pow] at hpow
  have h := hpow.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hx (Finset.mem_range.mp hj)) (pow_nonneg (by linarith : 0≤a+1) _))
  simpa only [mul_comm,mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left h (norm_nonneg (((-1:ℂ)^j)/(j+1:ℂ)))

variable {V : Type} [DecidableEq V] [Fintype V] (Γ : Census V)
private theorem positive {a : ℝ} (ha : 0≤a) : 0≤connectedBill Γ a := log_pos _
  (mul_nonneg (Nat.cast_nonneg _) (exp_pos _ ha))
private theorem mono {a b : ℝ} (ha : 0≤a) (h : a≤b) : connectedBill Γ a≤connectedBill Γ b :=
  log_mono _ (mul_nonneg (Nat.cast_nonneg _) (exp_pos _ ha))
    (mul_le_mul_of_nonneg_left (exp_mono _ ha h) (Nat.cast_nonneg _))

theorem scale {a x : ℝ} (ha : 0≤a) (hx : 1≤x) :
    connectedBill Γ (a*x)≤x^(Fintype.card V*Fintype.card V)*connectedBill Γ a := by
  let v := Fintype.card V
  have h := exp_scale v ha hx
  have cap : (Fintype.card Γ.Mode:ℝ)*expBill v (a*x)≤((Fintype.card Γ.Mode:ℝ)*expBill v a)*x^v := by
    simpa only [mul_comm,mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card Γ.Mode))
  have e := log_mono v (mul_nonneg (Nat.cast_nonneg _) (exp_pos v (mul_nonneg ha (zero_le_one.trans hx)))) cap
  simpa only [connectedBill,←pow_mul] using e.trans (log_scale v (mul_nonneg (Nat.cast_nonneg _) (exp_pos v ha)) (one_le_pow₀ hx))

variable {G : Gauge} (R : Run G) (hG : G.Simple) {J : Request V} (A : NumericSchedule R.family J)

def constant : ℝ := ((Fintype.card V*(J.inputPacketPowerCap+J.inputPacketRankCap)+1:ℕ):ℝ)*
  connectedBill Γ (Fintype.card V)

include hG in
/-- This is a true all-marks, all-coarse-field statement about the normalized
Wilson conditional, with the numerical cutoff prior to every datum and input.
Its low part is the polynomial in total incoming regular engineering degree. -/
theorem purchased (k : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d) (P₀ : MarkedPackets J.tests G (R.family.side (d.level+1) d.period) Γ),
      P₀.Paid (A.inputNorm d.level) F.inputAddresses F.inputRegion (fun v=>F.inputRadii v/F.kernelCosts v) 1
        (A.inputWidth d.level) (A.admittedCost d.level) F.coverOffset F.coverSlope→
      P₀.powerCap≤J.inputPacketPowerCap→P₀.rankCap≤J.inputPacketRankCap→∀ (x : IndependentTests J.tests)
      (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g := regulatorRun R.family d.cutoff d.period (d.level+1)
      let p₀ := (R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
      let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ p₀ g x) z)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
          constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  let v := Fintype.card V
  let K := (J.inputPacketRankCap+1)*(v*v)
  obtain ⟨start,spend⟩ := absorb A K (k+1) δ hδ
  filter_upwards [eventually_ge_atTop start,
      (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)]
    with m ready small d hd F P₀ paid hpw hr x U s
  subst m
  let g := regulatorRun R.family d.cutoff d.period (d.level+1)
  let b := A.admittedCost d.level
  let l := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
  have hg : 0<g := IterationFour.Currency.g_pos R.makes _ _ _ d.below
  have weak : g≤1 := (small d.cutoff d.period d.below).le
  obtain ⟨p,hp,he,h⟩ := ManuscriptQLocalPhysicalConditional.bare R d F P₀ paid weak x U s k
  refine ⟨p,hp,he,h.trans ?_⟩
  have hb : 1≤b := A.admitted_cost_ge_one _
  have hl : l≤v*(J.inputPacketPowerCap+J.inputPacketRankCap) := by
    simpa [l,v,ManuscriptQLocalShiftLedger.weight] using
      Nat.mul_le_mul (Finset.card_le_univ s.val) (Nat.add_le_add hpw hr)
  have h1 : (v:ℝ)*(b^P₀.rankCap*b)≤v*b^(J.inputPacketRankCap+1) := by
    rw [←pow_succ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (Nat.succ_le_succ hr)) (Nat.cast_nonneg _)
  have cmp := mono Γ (mul_nonneg (Nat.cast_nonneg v) (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (zero_le_one.trans hb))) h1
  have hc : connectedBill Γ ((v:ℝ)*(b^P₀.rankCap*b)) ≤ b^K*connectedBill Γ v := by
    simpa only [K,v,←pow_mul] using cmp.trans (scale Γ (Nat.cast_nonneg v) (one_le_pow₀ hb))
  have h0 := positive Γ (Nat.cast_nonneg v)
  have hs := spend d.level ready d.cutoff d.period d.below hg weak
  have hp0 : 0≤g^(k+1)*connectedBill Γ ((v:ℝ)*(b^P₀.rankCap*b)) := mul_nonneg (pow_nonneg hg.le (k+1)) (positive Γ
    (mul_nonneg (Nat.cast_nonneg v) (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (zero_le_one.trans hb))))
  calc _ ≤ ((v*(J.inputPacketPowerCap+J.inputPacketRankCap)+1:ℕ):ℝ)*(g^(k+1)*(b^K*connectedBill Γ v)) := by
         exact mul_le_mul (by exact_mod_cast Nat.succ_le_succ hl) (mul_le_mul_of_nonneg_left hc (pow_nonneg hg.le _)) hp0 (by positivity)
       _ = constant (J:=J) Γ*(b^K*g^(k+1)) := by unfold constant;ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg _) h0)

include hG in
theorem original (k : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d) (ξ : ℂ),‖ξ‖=1→∀ (x : IndependentTests J.tests)
      (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g := regulatorRun R.family d.cutoff d.period (d.level+1)
      let P₀ := ManuscriptQLocalPacketGrades.phaseSource F.packets g ξ
      let p₀ := (R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
      let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ p₀ g x) z)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
          constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  filter_upwards [purchased Γ R hG A k hδ,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)] with m h small d hd F ξ hξ x U s
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  subst m
  have weak := (small d.cutoff d.period d.below).le
  exact h d rfl F _ (ManuscriptQLocalPacketGrades.phase_earned F.packets F.input_paid hg weak ξ hξ)
    F.power_bounded F.rank_bounded x U s

include hG in
/-- The original signed Laurent grading at every auxiliary value. In particular the original startup economy, whose powers are all zero, incurs no separate displacement. -/
theorem nonpositive (k : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d),(∀i,F.packets.power i≤0)→∀ (x : IndependentTests J.tests)
      (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g := regulatorRun R.family d.cutoff d.period (d.level+1)
      let P₀ := F.packets
      let p₀ := (R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
      let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ p₀ g x) z)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
          constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  filter_upwards [purchased Γ R hG A k hδ,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)] with m h small d hd F hp x U s
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  subst m
  have weak := (small d.cutoff d.period d.below).le
  exact h d rfl F F.packets (ManuscriptQLocalOriginalGradeTariff.unweighted F.packets F.input_paid hg weak hp)
    F.power_bounded F.rank_bounded x U s

/-- At the positive physical coupling, take phase one inside the complete
normalized moment and its connected logarithm on each actual coarse field. -/
theorem measured (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d)
    (x : IndependentTests J.tests) (U : Config G (R.family.side d.level d.period)) :
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let B := (R.family.path.rep d.cutoff d.period (d.level+1)).p
    let P₀ := ManuscriptQLocalPacketGrades.phaseSource F.packets g 1
    Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ B g x) 1) =
      Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets B g x) 1) := by
  dsimp only
  apply congrArg
  unfold ManuscriptQLocalRegularConditional.moment
  apply congrArg
  funext T
  unfold ManuscriptQLocalRegularConditional.charged
  have hg : Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)≠0 :=
    (IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below).ne'
  rw [ManuscriptQLocalPreparedConditional.physical F.packets
    (R.family.path.rep d.cutoff d.period (d.level+1)).p hg x T]

omit [Fintype V] in
private lemma substitute_cost {S T:Poly Γ} (h:S=T) (s:Γ.Mode) (a:ℂ) (w b:ℝ) (paid:w*‖S.part s-a‖≤b):
    w*‖T.part s-a‖≤b := h ▸ paid

include hG in
/-- Original measured input at the physical point. The canonical graded
polynomial is pinned at every marker value and realized on the old input. -/
theorem physical (k : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d) (x : IndependentTests J.tests)
      (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g := regulatorRun R.family d.cutoff d.period (d.level+1)
      let P₀ := ManuscriptQLocalPacketGrades.phaseSource F.packets g 1
      let p₀ := (R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
      let L z := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ p₀ g x) z)
      let raw := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets p₀ g x) 1)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧ p.eval 1=raw.part s ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖raw.part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖ ≤
          constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  filter_upwards [original Γ R hG A k hδ] with m h d hd F x U s
  obtain ⟨p,hp,he,hs⟩ := h d hd F 1 norm_one x U s
  have hL := measured Γ R A d F x U
  exact ⟨p,hp,he,(he 1).trans (congrArg (fun z=>Poly.part z s) hL),substitute_cost Γ hL s _ _ _ hs⟩

end YM.Integration.ManuscriptQLocalRegularCalendar
end
