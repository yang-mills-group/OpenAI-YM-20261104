import YM.Integration.FullQLocalRetainedOutput
import YM.Integration.NativePreResetExponent

/-! The submitted inherited ordinary activity and the entire submitted forced
    bank on the original Wilson step. Prescribed layers and calibration are
    explicit multiplicative insertions on the complete marked density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedPhysicalInlet
open Function Filter Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Held RG3.Script.Picnic
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J} {z : LocalFormal.Datum C Γ}
    {F : AnalyticInput J A z} {η : ℝ} (I : FullPreparedInputAt F η)
local notation "p₁" => A.inputNorm z.level
local notation "Y₁" => C.path.rep z.cutoff z.period (z.level+1)
local notation "B₁" => I.carrier.rep
local notation "g₁" => Pert.Asymptotics.regulatorRun C z.cutoff z.period (z.level+1)

def bank : Activities G (C.side (z.level+1) z.period) :=
  ⟨I.error.labels,(B₁).activities.forced,I.error.action,(B₁).activities.K⟩

def rep : Rep G (C.side (z.level+1) z.period) :=
  {Y₁ with clip := (B₁).clip, p := p₁, v := (B₁).v, activities := bank I}

theorem original (hi : Retained.NativeIntake I) :
    (bank I).KBound (C.path.levels.budget (z.level+1)) (C.path.levels.clock.forcedAllowance (z.level+1)) :=
  hi.original

theorem valid (hi : Retained.NativeIntake I) :
    (bank I).Valid (p₁) I.inherited (C.path.levels.clock.forcedAllowance (z.level+1)) := by
  have h := I.error_paid
  have hk := I.wellFormed.forced
  have ht := I.wellFormed.threshold
  refine ⟨⟨h.smooth,h.flat,h.null⟩,⟨hk.sym,hk.symtest,hk.meas,hk.meas_test,?_,?_,?_⟩,
    ?_,h.credit,hi.reserved⟩
  · intro i
    rw [ht]
    exact hk.reads i
  · intro i
    rw [ht]
    exact hk.reads_test i
  · intro i U live
    change ((B₁).activities.forced i).eligible (p₁).threshold U
    rw [ht]
    exact hk.permit i U live
  intro s b
  obtain ⟨π,hπ⟩ := h.moves s b
  obtain ⟨ρ⟩ := I.wellFormed.moves s b
  exact ⟨⟨π,ρ.kp,fun i => (hπ i).1,fun i => (hπ i).2.1,ρ.forced_support,
    ρ.forced_inventory,ρ.forced_tests,fun i => (hπ i).2.2,ρ.valuesK⟩⟩

theorem lawful (hi : Retained.NativeIntake I) {σ A₀ Λ : ℝ}
    (hw : (Y₁).path.Bounds (Y₁).clip σ A₀ Λ) :
    (rep I).Lawful σ A₀ Λ I.inherited (C.path.levels.clock.forcedAllowance (z.level+1)) :=
  ⟨by change (Y₁).path.Bounds (B₁).clip σ A₀ Λ; rw [I.carrier.clip]; exact hw,valid I hi⟩

def insertion (U : Config G (C.side (z.level+1) z.period)) : ℝ :=
  Render.renders (Render.prefactor (g₁)) (B₁).p U F.layers + I.calibration.amount U

theorem exponent (U : Config G (C.side (z.level+1) z.period)) :
    (B₁).exponent U = (rep I).exponent U - insertion I U := by
  have path := NativePreResetExponent.channels_same_threshold (Y₁).path (B₁).clip
    (p₁) (B₁).p I.wellFormed.threshold (Y₁).beta U
  rw [I.exponent]
  change (B₁).scalar - ((Y₁).path.inChannels (B₁).clip (B₁).p (Y₁).beta U + _) - _ - _ =
    (B₁).scalar - (Y₁).path.inChannels (B₁).clip (p₁) (Y₁).beta U -
      I.error.amount (p₁) U - (_ + I.calibration.amount U)
  rw [path]
  ring

theorem gas (U : Config G (C.side (z.level+1) z.period)) :
    (rep I).activities.gas (p₁) U = (B₁).activities.gas (B₁).p U := by
  apply tsum_congr
  intro b
  have valid : (rep I).activities.admissible (p₁) U b = (B₁).activities.admissible (B₁).p U b := by
    simp only [Activities.admissible,rep,bank,I.wellFormed.threshold]
  change (if (rep I).activities.admissible (p₁) U b then ∏ i∈b,(B₁).activities.K i U else 0)=
    (if (B₁).activities.admissible (B₁).p U b then ∏ i∈b,(B₁).activities.K i U else 0)
  rw [valid]

theorem density (U : Config G (C.side (z.level+1) z.period)) :
    (B₁).eval U = Real.exp (-insertion I U) * (rep I).eval U := by
  unfold Rep.eval
  rw [exponent I,sub_eq_add_neg,Real.exp_add]
  change _ = _ * (_ * (rep I).activities.gas (p₁) U)
  rw [gas I]
  ring

def carried {X : Type} {o : V → Site (C.side (z.level+1) z.period)} (T : Taste X o (B₁) Γ) :
    Taste X o (rep I) Γ where
  menu := ⟨T.menu.origins,T.menu.rays,T.menu.branch,T.menu.marks,T.menu.global,T.menu.regular,T.menu.force⟩
  root := T.root
  tag := T.tag
  site := T.site
  score := T.score

variable {X : Type} {o : V → Site (C.side (z.level+1) z.period)}

theorem log (T : Taste X o (B₁) Γ) (x : X) (U : Config G (C.side (z.level+1) z.period)) :
    ((carried I T).leaf x).log U=(T.leaf x).log U := by
  simp only [Deck.log,Bands.extra,Bands.ray,Taste.leaf,View.terms,carried,rep,I.wellFormed.threshold]

theorem cluster (T : Taste X o (B₁) Γ) (x : X) (U : Config G (C.side (z.level+1) z.period)) :
    ((carried I T).leaf x).contents.cluster U=(T.leaf x).contents.cluster U := by
  simp only [Bands.cluster,Bands.packet,Bands.each,Bands.tagged,Activities.admissible,
    Taste.leaf,View.terms,carried,rep,bank,I.wellFormed.threshold]

theorem marked (T : Taste X o (B₁) Γ) (x : X) (U : Config G (C.side (z.level+1) z.period)) :
    (T.leaf x).density U=(Real.exp (-insertion I U):ℂ) • ((carried I T).leaf x).density U := by
  unfold Deck.density
  rw [log I T,cluster I T,exponent I,sub_eq_add_neg,Real.exp_add,Complex.ofReal_mul,smul_smul,mul_comm]

theorem active (T : Taste X o (B₁) Γ) (x : X) (h : (T.leaf x).Active)
    (reg : ∀ i, (p₁).Regular (T.menu.branch i) (T.menu.regular x i)) :
    ((carried I T).leaf x).Active := by
  have hb := h.articles
  refine ⟨⟨hb.proper,hb.pins,reg,hb.occurs,hb.retained,?_,?_,hb.meas,hb.invi⟩,h.captions⟩
  · intro i j
    change UsesFinal (p₁).threshold ((B₁).activities.forced i).support (T.menu.force x i j)
    rw [I.wellFormed.threshold]
    exact hb.inspects i j
  · intro i j U live
    change ((B₁).activities.forced i).eligible (p₁).threshold U
    rw [I.wellFormed.threshold]
    exact hb.keeps i j U live

def budget (T : Taste X o (B₁) Γ) {w : V → ℝ} {κ a b : ℝ} (h : FullBudget (p₁) T w κ a b) :
    FullBudget (p₁) (carried I T) w κ a b where
  white := h.white
  black := h.black
  gold := h.gold
  unitBound := h.unitBound
  active x := active I T x (h.active x) (h.regular_law x)
  radii := h.radii
  divisor := h.divisor
  white_nonnegative := h.white_nonnegative
  regular i := ⟨(h.regular i).controls⟩
  regular_law := h.regular_law
  black_nonnegative := h.black_nonnegative
  forced := h.forced
  gold_nonnegative := h.gold_nonnegative
  caption := h.caption
  unit_nonnegative := h.unit_nonnegative
  unit := h.unit
  regularTotal := h.regularTotal
  forcedTotal := h.forcedTotal

def reserve (T : Taste X o (B₁) Γ) {w : V → ℝ} {κ a b : ℝ} {cost : Γ.Mode → ℝ}
    (h : RelativeBudget (p₁) T w κ cost a b) : RelativeBudget (p₁) (carried I T) w κ cost a b :=
  ⟨h.positive,h.quiet,budget I (priceNormalized cost T) h.budget⟩

def remainder : RelativeBudget (p₁)
    (carried I (pullback (testInclusion J.tests) I.prepared.remainder)) F.inputRadii
    (forcedDivisor C (z.level+1)) (envelopeProduct F.kernelCosts) I.regularPrice I.forcedPrice :=
  reserve I _ I.prepared.remainder_price

theorem prepared (x : TestSpace J.tests) (U : Config G (C.side (z.level+1) z.period)) :
    (I.input.leaf x).density U = (Real.exp (-insertion I U):ℂ) •
      (Poly.pass (F.packets.read x (g₁) U) * ((carried I I.prepared.remainder).leaf x).density U) := by
  calc
    _ = Poly.pass (F.packets.read x (g₁) U) * (I.prepared.remainder.leaf x).density U := I.prepared.full x U
    _ = _ := (congrArg (fun Z => Poly.pass (F.packets.read x (g₁) U)*Z)
      (marked I I.prepared.remainder x U)).trans (mul_smul_comm ..)

end YM.Integration.QLocalInheritedPhysicalInlet
end
