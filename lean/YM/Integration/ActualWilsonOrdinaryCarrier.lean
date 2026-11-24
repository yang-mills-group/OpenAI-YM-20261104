import YM.Integration.ActualWilsonAxisSpectator
import YM.Integration.LocalComparisonVacuumRemainder
import YM.Integration.KBoundGas

/-! The complete ordinary part of the selected insertion on the original
Wilson representative, with its original nonzero vacuum activities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonOrdinaryCarrier
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open RG3.Forms RG3.Held Overlay Extra.Histories Relay
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato ActualWilsonAxisSpectator
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ξ : Type} [DecidableEq V] {B : Census V}
    {o : V → Site n} {X : Rep G n}

/-- Preserve all input regular supports, rays, functions, units and captions,
and use the recipient vacuum with zero marked deviations of its activities. -/
def copy (W : Rep G n) (T : Taste Ξ o X B) : Taste Ξ o W B where
  menu :=
    { origins := T.menu.origins
      rays := T.menu.rays
      branch := T.menu.branch
      marks := T.menu.marks
      global := T.menu.global
      regular := T.menu.regular
      force := fun _ _ _ _ => 0 }
  root := T.root
  tag := T.tag
  site := T.site
  score := T.score

theorem active (W : Rep G n) (T : Taste Ξ o X B) (x : Ξ)
    (hw : W.p=X.p) (hd : (T.leaf x).Active) : ((copy W T).leaf x).Active := by
  refine ⟨⟨hd.articles.proper,hd.articles.pins,fun j => ?_,hd.articles.occurs,
    fun i j hn => False.elim (hn rfl),fun i j U F _ _ => rfl,
    fun i j U hn => False.elim (hn rfl),fun i j => measurable_const,fun i j g U => rfl⟩,
    hd.captions⟩
  rw [hw]
  exact hd.articles.regular j


/-- Copying the ordinary part preserves the whole regular budget. The
recipient vacuum remains in its own activities and every marked deviation
of a forced row has zero cost. -/
def budget (W : Rep G n) (T : Taste Ξ o X B) {p : BudgetPoint} {θ : V → ℝ}
    {κ reg fro : ℝ} (hw : W.p=X.p) (H : FullBudget p T θ κ reg fro) :
    FullBudget p (copy W T) θ κ reg fro where
  white := H.white
  black := fun _ => 0
  gold := H.gold
  unitBound := H.unitBound
  active := fun x => active W T x hw (H.active x)
  radii := H.radii
  divisor := H.divisor
  white_nonnegative := H.white_nonnegative
  regular := fun j => ⟨(H.regular j).controls⟩
  regular_law := H.regular_law
  black_nonnegative := fun _ => le_rfl
  forced := fun _ _ _ _ => by simp [copy]
  gold_nonnegative := H.gold_nonnegative
  caption := H.caption
  unit_nonnegative := H.unit_nonnegative
  unit := H.unit
  regularTotal := H.regularTotal
  forcedTotal := by
    intro v
    apply Push.AbsoluteSums.budget_mono (H.forcedTotal v)
    · intro j
      simp only [BudgetPoint.mass,mul_zero,ite_self,le_refl]
    intro j
    simp only [BudgetPoint.mass,mul_zero,ite_self]
    exact (H.forcedTotal v).1 j

variable [Fintype V]

theorem log_eq (W : Rep G n) (T : Taste Ξ o X B) (x : Ξ)
    (hw : W.p.threshold=X.p.threshold) (U : Config G n) :
    ((copy W T).leaf x).log U=(T.leaf x).log U := by
  change ((∑ v, Poly.send (B.fire v) (T.menu.global x v))+
    ∑' i, Poly.send (T.menu.rays i) (masked W.p.threshold (T.menu.branch i) (T.menu.regular x i) U))+
      (T.leaf x).captions.chord = _
  rw [hw]
  rfl

omit [Fintype V] in
/-- The packet is the original Wilson vacuum packet on the original labels. -/
theorem packet (W : Rep G n) (T : Taste Ξ o X B) (x : Ξ)
    (s : Finset ℕ) (U : Config G n) : ((copy W T).leaf x).contents.packet s U =
      Poly.bead B (W.activities.gasOccurrence W.p s U : ℂ) :=
  vacuumRemainder_packet (copy W T) x s U

theorem density (W : Rep G n) (T : Taste Ξ o X B) (x : Ξ)
    (hw : W.p.threshold=X.p.threshold) {w : ℝ} (hK : W.activities.KBound W.p w)
    (U : Config G n) : ((copy W T).leaf x).density U =
      (W.eval U : ℂ) • Poly.pass ((T.leaf x).log U) := by
  have hGas := (Activities.gasSeries_of_KBound hK).absolute U
  have hSend : Summable (fun s : Finset ℕ => Poly.bead B (W.activities.gasOccurrence W.p s U : ℂ)) := by
    apply (Poly.budgeted (fun _ => zero_lt_one) hGas ?_).1
    intro s
    change Poly.price (fun _ => (1:ℝ)) (Poly.send B.quiet (W.activities.gasOccurrence W.p s U : ℂ)) ≤ _
    rw [Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real]
  have hCluster : ((copy W T).leaf x).contents.cluster U =
      Poly.bead B (W.activities.gas W.p U : ℂ) := by
    change (∑' s,((copy W T).leaf x).contents.packet s U) = _
    simp_rw [packet]
    ext j
    rw [Poly.share hSend]
    change (∑' s, (Poly.send B.quiet
      (W.activities.gasOccurrence W.p s U : ℂ)).part j) =
      (Poly.send B.quiet (W.activities.gas W.p U : ℂ)).part j
    simp only [Poly.part_send]
    by_cases hj : j = B.quiet
    · subst j
      simp only [ite_true, Activities.gas, Complex.ofReal_tsum]
    simp only [if_neg hj, tsum_zero]
  unfold Deck.density
  rw [log_eq W T x hw U,hCluster,mul_comm _ (Poly.bead B (W.activities.gas W.p U : ℂ)),Poly.product_bead,smul_smul]
  congr 1
  exact (Complex.ofReal_mul _ _).symm

/-- The raw, unnormalized chosen ordinary field is a complete physical
singleton density on the original Wilson carrier. -/
theorem selected (R : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) {δ : ℝ} {a : ℕ} (H : Bounds S δ a)
    (x : IndependentTests J.tests) (v : V) :
    let W := R.family.path.rep datum.cutoff datum.period datum.level
    let T := pullback (testInclusion J.tests) S.output.residual
    ∀ U, (((copy W T).leaf x).density U).part (B.fire v) = ordinary R S x v U := by
  intro W T U
  have hw : W.p = R.family.path.levels.budget datum.level :=
    (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).vac
  have hX := hw.trans S.output.carrier.point.symm
  have hK := (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good.labels.boundK
  have hzero : ((T.leaf x).log U).part B.quiet = 0 := by
    rw [log_constant_split, Poly.part_plus,
      H.residual_price.constantLog_quiet F.kernel_positive S.wellFormed.threshold,
      H.residual_price.nativeRayLog_quiet F.kernel_positive S.wellFormed.threshold,add_zero]
  rw [density W T x (congrArg BudgetPoint.threshold hX) hK U,Poly.part_smul,
    MergeProof.Accent.whisper B _ hzero]
  rfl

end YM.Integration.ActualWilsonOrdinaryCarrier
