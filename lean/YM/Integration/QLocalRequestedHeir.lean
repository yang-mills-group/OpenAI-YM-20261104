import YM.Integration.QLocalInheritedNativeStage
import YM.Integration.QLocalInheritedSourcePrice
import YM.Integration.QLocalInheritedCoverPurchase

/-! Requested derivative orders on the original two-ended Gaussian step.
    The physical block order and all path, metric and covariance data are fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRequestedHeirQuote
open Filter Function Set Lattice Wilson Pressure RG Tree Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm
open Marker Comparison.RG02 IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep LocalComparison LocalComparison.Global Next.SectorChange
open Push.PriceCompiler Supply Testing AnalyticBridge.LocalGaussianLaws
open AnalyticBridge.VerifiedReset.Time
open scoped Classical

variable {G : Gauge} {V : Type} (J : Request V)

def teller (P : Teller G) : Teller G := { P with
  top := {P.top with
    order:=J.inputFieldOrder, power:=J.inputDistanceOrder, supportExponent:=J.inputSupport
    order_ge:=J.field_minimum.trans J.field_reserve, power_ge:=J.distance_minimum.trans J.distance_reserve
    price_pos:=J.input_support_pos}
  below := {P.below with
    order:=J.outputFieldOrder, power:=J.outputDistanceOrder, supportExponent:=J.outputSupport
    order_ge:=J.field_minimum, power_ge:=J.distance_minimum, price_pos:=J.output_support_pos} }

theorem funds {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S}
    (h : P.Funds S T) : (teller J P).Funds S T :=
  ⟨h.knobs,h.atStep,h.kernel,h.crosses,h.low,h.high,h.feeds,h.tilts⟩

theorem booth {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S}
    (h : Lift.Booth P S T) : Lift.Booth (teller J P) S T :=
  ⟨funds J h.1,h.2⟩

theorem window {P : Teller G} {δ K : ℝ} (hd : 0<δ) (hK : 0≤K) :
    ∃ C : Libretto G J.outputFieldOrder, C.δ=δ ∧ C.N=K ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), (teller J P).Funds S T →
        ∀ F, Matins T F J.inputDistanceOrder (2*C.C) C.M :=
  leads (teller J P) δ K hd hK

def toll (J : Request V) := J.outputSupport+3

theorem tariff (C : Libretto G J.outputFieldOrder) :
    ∃ E, Release.Quotation C J.outputDistanceOrder 505 J.inputSupport (toll J) E :=
  Release.quoting C J.outputDistanceOrder 505 J.input_support_pos (by unfold toll; linarith [J.output_support_pos])

/-- The true fields and their initial configuration are untouched by the order
    change. This contract is uniform in the coarse period and every submitted
    source. Its post-length record is chosen before the coarse inverse coupling. -/
structure Ready (old : Teller G) (H : Patch) (C : Libretto G J.outputFieldOrder)
    (D : Heir.Record) (x : ℝ) : Prop where
  price (P B : BudgetPoint) :
    P.threshold=temp x → B.threshold=fiery G x H.L → B.B=radiusB (betaF G x H.L) →
    P.order=J.outputFieldOrder → B.order=J.inputFieldOrder →
    P.power=J.outputDistanceOrder → B.power=J.inputDistanceOrder →
    (∀ β, betaF G x H.L/2≤β →
      0<coupling β ∧ Lute.Plented C D P B H.L 505 x (coupling β)) ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=H →
      Seam T C.δ C.N → Lift.Booth old S T → 100*(1+radiusB x)≤c.val →
      Plays C D P B (teller J old) T x

theorem songs (old : Teller G) (H : Patch) (C : Libretto G J.outputFieldOrder)
    (branches : H.Branches old.bind G) (gate : licensed C.δ C.N H.L)
    (stage : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), (teller J old).Funds S T →
      ∀ F, Matins T F J.inputDistanceOrder (2*C.C) C.M) {cap : ℝ} (hc : 0<cap) :
    ∃ D : Heir.Record, D.ε≤cap ∧ Tight C D ∧ ∀ᶠ x : ℝ in atTop, Ready J old H C D x := by
  obtain ⟨D,hD,hC,hx⟩ := Heir.songs H (teller J old) C branches gate J.field_reserve J.distance_reserve stage 505 cap hc
  refine ⟨D,hD,hC,hx.mono fun x h => ⟨fun P B ht hf hB hp hO hd hd' => ?_⟩⟩
  have p := h P B ht hf hB hp hO hd hd'
  exact ⟨p.1,fun S T he hs hb => p.2 S T he hs (booth J hb)⟩

end YM.Integration.QLocalRequestedHeirQuote
end

/-! An alternative real requested-order Heir libretto, obtained before the
    original lengths and priced before the selected physical beta. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRequestedHeirPurchase
open Function Set Filter Lattice Wilson RG Marker Pressure Precision Tree
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open FullQLocal FullQLocal.RenderedStep WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} (J : Request V)
variable (s : Sheet G) (K : MapPrices)

def libretto (j i : ℕ) : Libretto G J.outputFieldOrder :=
  (window J (P:=query s K j i) (wide_pos K j i) (scale_nn K j i)).choose

theorem calibrated (j i : ℕ) :
    (libretto J s K j i).δ=wide K j i ∧ (libretto J s K j i).N=scale K j i ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), (teller J (query s K j i)).Funds S T →
       ∀ F, Matins T F J.inputDistanceOrder (2*(libretto J s K j i).C) (libretto J s K j i).M :=
  (window J (P:=query s K j i) (wide_pos K j i) (scale_nn K j i)).choose_spec

def wage (j i : ℕ) := QLocalInheritedSourcePrice.fee J (libretto J s K j i) 505

structure Earlier (extra : Stage → ℕ → ℝ) (j i L : ℕ) : Prop where
  support : 20*Release.base (toll J) 505≤(L:ℝ)*J.inputSupport
  seam : yarn (libretto J s K j i).δ (libretto J s K j i).N≤(L:ℝ)^2/128
  payment : ((1+|extra (s.profile i) i|)*|wage J s K j i|)*(1+(j:ℝ))≤(L:ℝ)

theorem Earlier.raised {extra : Stage → ℕ → ℝ} {j i length : ℕ}
    (h : Earlier J s K extra j i length) (floor : ℕ → ℕ) :
    Earlier J (ThroughLaunch.raise s floor) K extra j i length :=
  ⟨h.support,h.seam,h.payment⟩

theorem earlier (extra : Stage → ℕ → ℝ) (j i : ℕ) :
    ∀ᶠ L : ℕ in atTop, Earlier J s K extra j i L := by
  have rising := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [(rising.atTop_mul_const J.input_support_pos).eventually_ge_atTop
      (20*Release.base (toll J) 505),
    rising.eventually_ge_atTop (128*yarn (libretto J s K j i).δ (libretto J s K j i).N),
    rising.eventually_ge_atTop 1,
    rising.eventually_ge_atTop (((1+|extra (s.profile i) i|)*|wage J s K j i|)*(1+(j:ℝ)))] with L ht hY hL hP
  exact ⟨ht,by nlinarith only [hY,hL],hP⟩

def Paid (extra : Stage → ℕ → ℝ) : Prediction G := fun {M} {L} {A} _ =>
  ∃ rec : ℕ → ℕ → Heir.Record,
    (∀ j i, StepStages j i → Earlier J M.p M.K extra j i (L.L j).val) ∧
    ∀ j x, A.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
      Ready J (query M.p M.K j i) (Clockwork.patch L st fr) (libretto J M.p M.K j i) (rec j i) x

theorem prepaid (extra : Stage → ℕ → ℝ) : Prepaid (QLocalRequestedHeirPurchase.Paid (G:=G) J extra) s K := by
  intro _ _ _ _ _ _ _
  obtain ⟨u,_,_,h⟩ := collect_upper s.floorL (fun j L => ∀ i, StepStages j i → Earlier J s K extra j i L)
    (fun j=>eventually_transitions j _ _ (fun i _=>earlier J s K extra j i))
  refine ⟨u,fun l hl L _ _ _ _ _ _ _ _ V' _ => ?_⟩
  have gate (j i) (step : StepStages j i) : Earlier J s K extra j i (L.L j).val :=
    h j _ ((hl j).trans (L.large j).need) i step
  have rows (j i : ℕ) : ∃ D : Heir.Record, ∀ᶠ x : ℝ in atTop,
      ∀ (st : StepStages j i) (fr : s.first ≤ i),
        Ready J (query s K j i) (Clockwork.patch L st fr) (libretto J s K j i) D x := by
    by_cases hi : (StepStages j i ∧ (s.first ≤ i))
    · let H := Clockwork.patch L hi.1 hi.2
      obtain ⟨D,_,_,hD⟩ := QLocalRequestedHeirQuote.songs J (query s K j i) H (libretto J s K j i)
        (s.has _) (gate j i hi.1).seam (calibrated J s K j i).2.2 (show 0<(1/4:ℝ) by norm_num)
      exact ⟨D,hD.mono fun _ hx _ _=>hx⟩
    exact ⟨Suite.one,Eventually.of_forall fun _ hs hf=>(hi ⟨hs,hf⟩).elim⟩
  choose rec hrec using rows
  obtain ⟨β,_,hβ,h'⟩ := collect_upper V'.betaEntry _
    (fun j=>eventually_transitions j _ _ (fun i _=>hrec j i))
  refine ⟨{V' with betaEntry:=β},⟨hβ,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW B I hp B' A η q E' X J' K' b hZ hY hm
  exact ⟨rec,fun j i st=>Earlier.raised J s K (gate j i st) l,
    fun j x hx i st fr=>h' j x ((hW.beta j).trans hx) i st st fr⟩

end YM.Integration.QLocalRequestedHeirPurchase
end

/-! Apply the real requested-grade preselection to the inherited payload of
    every prepared interior step. All original label positions are retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalRequestedHeirSource
open Function Filter Set Lattice Wilson RG Tree Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open Pressure Supply Testing Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection VerifiedReset.Time LocalGaussian LocalGaussianLaws
open Marker Comparison.RG02 IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirPurchase QLocalRequestedHeirQuote
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    (R : Run G) {J : Request V} {extra : Stage → ℕ → ℝ} (paid : QLocalRequestedHeirPurchase.Paid J extra R.kit)
    (A : NumericSchedule R.family J) (datum : LocalFormal.Datum R.family Γ)
local notation "a₀" => R.alloy.B.a
local notation "m₀" => datum.level
local notation "i₀" => R.alloy.B.a.clock.J datum.level
local notation "i₁" => R.alloy.B.a.clock.J (datum.level+1)
local notation "S₀" => R.alloy.B.a.clock.op datum.level datum.period
local notation "x₀" => R.alloy.B.a.clock.hatBeta datum.level
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)
local notation "p₀" => A.outputNorm datum.level
local notation "p₁" => A.inputNorm datum.level
local notation "C₀" => libretto J R.metals.p R.metals.K (i₁) (i₀)
local notation "D₀" => paid.choose (i₁) (i₀)
local notation "Pt" => query R.metals.p R.metals.K (i₁) (i₀)
local notation "T₀" => ships R.alloy.B datum.cutoff datum.level datum.period

include paid

omit [Fintype V] in
theorem booked :
    Plays (C₀) (D₀) (p₀) (p₁) (teller J (Pt)) (T₀) (x₀) ∧
    Release.accepts 505 (p₁).supportExponent (Quotes.preExponent (p₀)) (S₀).patch.L ∧
    Lute.Plented (C₀) (D₀) (p₀) (p₁) (S₀).patch.L 505 (x₀) (g₁) := by
  let B := R.alloy.B
  let j := (i₁)
  let i := (i₀)
  have fr := first_le B.valid (m₀)
  have step := step_paid (a₀) (m₀)
  let H := Clockwork.patch R.rolls step fr
  have hL : (S₀).patch.L=R.rolls.L j := block_eq B.valid _
  have hJ : (S₀).patch.J=j := (Testing.proceeds B datum.cutoff (m₀) datum.period datum.below).atStep
  have patch : (S₀).patch=H := by
    cases hh : (S₀).patch
    rw [hh] at hL hJ
    unfold H Clockwork.patch
    congr
  have hr := paid.choose_spec.2 j (x₀) (B.valid.pays _) i step fr
  have hβ := beta_eq B.valid (m₀)
  have hpay := hr.price (p₀) (p₁) (A.output_norm _).threshold
    ((A.input_norm _).threshold.trans (congrArg temp hβ))
    ((A.input_norm _).block.trans (congrArg radiusB hβ))
    (A.output_norm _).order (A.input_norm _).order (A.output_norm _).distance (A.input_norm _).distance
  have below := datum.below
  have sworn i (hi : i∈({(m₀),(m₀)+1}:Set ℕ)) : Bid.Sworn (B.M.H datum.cutoff i) (B.a.S.side i datum.period) G := by
    apply R.kit.pledging.conducts.full
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi
    omega
  have bo : Lift.Booth (Pt) (S₀) (T₀) := Suite.booths_of datum.period B.M B.kin.path B.plan sworn
    (fun i hi => B.support.links _ _ (by simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi; omega))
    datum.below (Testing.proceeds B datum.cutoff (m₀) datum.period datum.below)
  have seam : Seam (T₀) (C₀).δ (C₀).N := by
    rw [(calibrated J R.metals.p R.metals.K j i).1,(calibrated J R.metals.p R.metals.K j i).2.1]
    exact Suite.seam_of datum.period B.M B.kin.path B.plan datum.below
  have hT := hpay.2 (S₀) (T₀) patch seam bo (by rw [add_comm 1]; exact (a₀).fits.sizeT _ _)
  have gate := (paid.choose_spec.1 j i step).support
  have hcomp := (R.makes.wilson.represents datum.cutoff datum.period (m₀+1) datum.below).band
  refine ⟨hT,?_,?_⟩
  · change 20*Release.base (Quotes.preExponent (p₀)) 505≤((S₀).patch.L.val:ℝ)*(p₁).supportExponent
    rw [hL,(A.input_norm _).reserve]
    unfold Quotes.preExponent
    rw [(A.output_norm _).reserve]
    exact gate
  rw [hL]
  exact (hpay.1 _ (hβ ▸ hcomp.1)).2

omit A [Fintype V] in
theorem weighted :
    (1+|extra (R.metals.p.profile (i₀)) (i₀)|)*
      (wage J R.metals.p R.metals.K (i₁) (i₀)/((S₀).patch.L.val:ℝ))≤
      (1+((i₁):ℝ))⁻¹ := by
  have h := (paid.choose_spec.1 (i₁) (i₀) (step_paid (a₀) (m₀))).payment
  have hL : (S₀).patch.L=R.rolls.L (i₁) := block_eq R.alloy.B.valid _
  rw [hL]
  have hpos : 0<(R.rolls.L (i₁)).val := (R.rolls.L (i₁)).property
  have hden : (0:ℝ)<(R.rolls.L (i₁)).val := Nat.cast_pos.mpr hpos
  have hz : 0<1+((i₁):ℝ) := by positivity
  rw [←mul_div_assoc,←one_div,div_le_div_iff₀ hden hz,one_mul]
  exact le_trans (by gcongr; exact le_abs_self _) h

omit [Fintype V] in
/-- One physical scale works for every later period and cutoff. -/
theorem small (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ z : LocalFormal.Datum R.family Γ, M≤z.level →
      let a := R.alloy.B.a
      let i := a.clock.J z.level
      let j := a.clock.J (z.level+1)
      (1+|extra (R.metals.p.profile i) i|)*
        (wage J R.metals.p R.metals.K j i/((a.clock.op z.level z.period).patch.L.val:ℝ))≤ε := by
  have hd : Tendsto (fun m : ℕ => (R.family.path.levels.clock.J m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.family.path.levels.fits.deep
  obtain ⟨M,hM⟩ := eventually_atTop.1 (hd.eventually_ge_atTop ε⁻¹)
  refine ⟨M,fun z late => (weighted R paid z).trans ?_⟩
  have h : ε⁻¹ ≤ 1+(R.alloy.B.a.clock.J (z.level+1):ℝ) := (hM (z.level+1) (by omega)).trans
    (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ (ε⁻¹)⁻¹ := (inv_le_inv₀ (by positivity) (inv_pos.mpr hε)).2 h
    _ = ε := inv_inv ε

variable {F : AnalyticInput J A datum} {η : ℝ} (I : FullPreparedInputAt F η)
local notation "L₀" => fun i => PhysicalNext.Repeat.headed (S:=S₀) (I.error.labels i) (x₀) 500

def Charged (χ q : Chi) (d H : ℝ) : Prop :=
  let hB : (p₀).B=radiusB (x₀) := (A.output_norm (m₀)).block
  let σ := fun i => QLocalInheritedPrincipalScroll.source (G:=G) (S₀) (p₁) (x₀) (g₁) (D₀)
    (I.error.labels i) χ 500 505 (hB ▸ (p₀).B_pos) (by decide) (by decide)
  let g := fun i => (σ i).tuning (g₁) q d (I.error.action i) (T₀)
  ∃ v : ℕ → ℝ, (∀ i, (p₀).Regular (L₀ i).support (g i) ∧
    (p₀).supBounds (L₀ i).site (L₀ i).support (g i) (v i)) ∧ Quotes.early (p₀) (L₀) v H

theorem fields (hG : G.Simple) (χ q : Chi) (d : ℝ) :
    Charged R paid A datum I χ q d
      (wage J R.metals.p R.metals.K (i₁) (i₀)/((S₀).patch.L.val:ℝ)*I.inherited) := by
  have h := booked R paid A datum
  exact QLocalInheritedSourcePrice.purchased R I (C₀) hG (T₀) (D₀) h.1 h.2.1 h.2.2 χ q d
    (by decide : 500≤500) (by decide : 500+5≤505)

/-- Independent marked tests, all cutoff volumes and all inherited signed fields
    use the same late scale. The weights include the full support reserve. -/
theorem contracted (hG : G.Simple) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ z : LocalFormal.Datum R.family Γ, M≤z.level →
      ∀ {F : AnalyticInput J A z} {η : ℝ} (I : FullPreparedInputAt F η) (χ q : Chi) (d : ℝ),
        Charged R paid A z I χ q d (ε*I.inherited) := by
  obtain ⟨M,hm⟩ := small (Γ:=Γ) R paid ε hε
  refine ⟨M,?_⟩
  intro z hz F η I χ q d
  obtain ⟨v,hv,hb⟩ := fields R paid A z I hG χ q d
  refine ⟨v,hv,fun x => budget_loosen (hb x) (mul_le_mul_of_nonneg_right ?_ I.inherited_nonnegative)⟩
  let a := R.alloy.B.a
  let i := a.clock.J z.level
  let j := a.clock.J (z.level+1)
  have hw : 0≤wage J R.metals.p R.metals.K j i := le_trans zero_le_one
    (QLocalInheritedSourcePrice.quote J (libretto J R.metals.p R.metals.K j i) 505).nonneg
  exact (le_mul_of_one_le_left (div_nonneg hw (by positivity))
    (le_add_of_nonneg_right (abs_nonneg (extra (R.metals.p.profile i) i)))).trans (hm z hz)

end YM.Integration.QLocalRequestedHeirSource
end
