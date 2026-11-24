import YM.Integration.QLocalRequestedSectorSale
import YM.Integration.QLocalRequestedSectorIntake

/-! The funded original interior sector, its actual incoming signed Cash and
    the native ordinary glyph on the same registered Heir record. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalRequestedSectorCalendar
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} (J : Request V) (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)

def Paid : Prediction G := fun {M} {D} {A} H =>
  ∃ b : ℕ → ℕ → Booking G,
    (∀ j i, StepStages j i → Earlier J M.p M.K extra j i (D.L j).val) ∧
    ∀ j x, A.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
      QLocalRequestedSectorSale.Window J Δ (H.target j i) (libretto J M.p M.K j i) (b j i)
        (Clockwork.patch D st fr) x γ ∧ Thermal G (D.L j) j (extra (M.p.profile i) i) x

theorem prepaid (hG : G.Simple) (hγ : -(1/2:ℝ)<γ) (s : Sheet G) (K : MapPrices) :
    Prepaid (Paid J Δ extra γ) s K := by
  intro Q E c C₀ z₂ b hW
  obtain ⟨u,_,_,h⟩ := collect_upper s.floorL
    (fun j L => ∀ i, StepStages j i → Earlier J s K extra j i L ∧ floor J (Q j i) Δ≤L)
    (fun j => eventually_transitions j _ _ (fun i _ =>
      (earlier J s K extra j i).and (eventually_ge_atTop (floor J (Q j i) Δ))))
  refine ⟨u,fun l hl D _ _ _ _ _ _ _ _ V' _ => ?_⟩
  have gate (j i) (st : StepStages j i) := h j (D.L j).val ((hl j).trans (D.large j).need) i st
  have rows (j i : ℕ) : ∃ b : Booking G, ∀ᶠ x : ℝ in atTop,
      ∀ (st : StepStages j i) (fr : s.first ≤ i),
        QLocalRequestedSectorSale.Window J Δ (Q j i) (libretto J s K j i) b (Clockwork.patch D st fr) x γ ∧
          Thermal G (D.L j) j (extra (s.profile i) i) x := by
    by_cases h : (StepStages j i ∧ (s.first ≤ i))
    · obtain ⟨b,hb⟩ := QLocalRequestedSectorSale.sale J hG Δ (Q j i) (Clockwork.patch D h.1 h.2)
        (libretto J s K j i) (s.has _) (gate j i h.1).1.seam (gate j i h.1).2
        (calibrated J s K j i).2.2 γ hγ
      exact ⟨b,(hb.and (thermal_after G (D.L j) j (extra (s.profile i) i))).mono fun _ hx _ _ => hx⟩
    exact ⟨vacant G,Eventually.of_forall fun _ st fr => (h ⟨st,fr⟩).elim⟩
  choose b hb using rows
  obtain ⟨β,_,hv,hβ⟩ := collect_upper V'.betaEntry _
    (fun j => eventually_transitions j _ _ (fun i _=>hb j i))
  refine ⟨{V' with betaEntry:=β},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW K' I' hp B' B η q E' X J' K'' b' hZ hY hm
  exact ⟨b,fun j i st => Earlier.raised J s K (gate j i st).1 l,
    fun j x hx i st fr => hβ j x ((hW.beta j).trans hx) i st st fr⟩

variable [DecidableEq V] [Fintype V] {Γ : Census V} (R : Run G)
    (paid : Paid J Δ extra γ R.kit) (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family Γ)
local notation "a₀" => R.alloy.B.a
local notation "m₀" => z.level
local notation "j₁" => (a₀).clock.J (m₀+1)
local notation "j₀" => (a₀).clock.J (m₀)
local notation "x₀" => (a₀).clock.hatBeta (m₀)
local notation "S₀" => (a₀).clock.op (m₀) z.period
local notation "T₀" => ships R.alloy.B z.cutoff (m₀) z.period
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "C₀" => libretto J R.metals.p R.metals.K (j₁) (j₀)
local notation "Q₀" => R.kit.target (j₁) (j₀)
local notation "b₀" => paid.choose (j₁) (j₀)

omit [Fintype V] in
theorem selected : QLocalRequestedSectorSale.Window J Δ (Q₀) (C₀) (b₀) (S₀).patch (x₀) γ := by
  have st := step_paid (a₀) (m₀)
  have fr := first_le R.alloy.B.valid (m₀)
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  have hJ : (S₀).patch.J=(j₁) := (Testing.proceeds R.alloy.B z.cutoff (m₀) z.period z.below).atStep
  have hP : (S₀).patch=Clockwork.patch R.rolls st fr := by
    cases h : (S₀).patch
    rw [h] at hL hJ
    unfold Clockwork.patch
    congr
  rw [hP]
  exact (paid.choose_spec.2 _ _ (R.alloy.B.valid.pays _) _ st fr).1

include paid in
omit [Fintype V] in
theorem thermal : Thermal G (S₀).patch.L (j₁) (extra (R.metals.p.profile (j₀)) (j₀)) (x₀) := by
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  rw [hL]
  exact (paid.choose_spec.2 _ _ (R.alloy.B.valid.pays _) _ (step_paid (a₀) (m₀)) (first_le R.alloy.B.valid _)).2

variable {F : AnalyticInput J A z} {η : ℝ} (I : FullPreparedInputAt F η)
local notation "Y₁" => QLocalInheritedPhysicalInlet.rep I
local notation "p₀" => A.outputNorm (m₀)
local notation "p₁" => A.inputNorm (m₀)

omit [Fintype V] in
theorem record_at (b : Booking G)
    (window : QLocalRequestedSectorSale.Window J Δ (Q₀) (C₀) b (S₀).patch (x₀) γ)
    (early : Earlier J R.metals.p R.metals.K extra (j₁) (j₀) (S₀).patch.L.val) : Plays (C₀) b.record (p₀) (p₁) (teller J (P₀)) (T₀) (x₀) ∧
    Release.accepts 505 (p₁).supportExponent (toll J) (S₀).patch.L ∧
    Lute.Plented (C₀) b.record (p₀) (p₁) (S₀).patch.L 505 (x₀)
      (Pert.Asymptotics.regulatorRun R.family z.cutoff z.period (m₀+1)) := by
  let B := R.alloy.B
  have hβ := Application.clock_next (a₀) (m₀) z.period
  have hr := window.heir.price (p₀) (p₁) (A.output_norm _).threshold
    ((A.input_norm _).threshold.trans (congrArg temp hβ))
    ((A.input_norm _).block.trans (congrArg radiusB hβ))
    (A.output_norm _).order (A.input_norm _).order (A.output_norm _).distance (A.input_norm _).distance
  have below := z.below
  have sworn i (hi : i∈({(m₀),(m₀)+1}:Set ℕ)) : Bid.Sworn (B.M.H z.cutoff i) (B.a.S.side i z.period) G := by
    apply R.kit.pledging.conducts.full
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi
    omega
  have bo : AnalyticBridge.LocalGaussianLaws.Lift.Booth (P₀) (S₀) (T₀) := Suite.booths_of z.period B.M B.kin.path B.plan sworn
    (fun i hi => B.support.links _ _ (by simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi; omega))
    z.below (Testing.proceeds B z.cutoff (m₀) z.period z.below)
  have seam : Seam (T₀) (C₀).δ (C₀).N := by
    rw [(calibrated J R.metals.p R.metals.K (j₁) (j₀)).1,
      (calibrated J R.metals.p R.metals.K (j₁) (j₀)).2.1]
    exact Suite.seam_of z.period B.M B.kin.path B.plan z.below
  refine ⟨hr.2 _ _ rfl seam bo (by rw [add_comm 1]; exact (a₀).fits.sizeT _ _),?_,?_⟩
  · change 20*Release.base (toll J) 505≤((S₀).patch.L.val:ℝ)*(p₁).supportExponent
    rw [(A.input_norm _).reserve]
    exact early.support
  exact (hr.1 _ (hβ ▸ (R.makes.wilson.represents z.cutoff z.period (m₀+1) z.below).band.1)).2

omit [Fintype V] in
theorem recording : Plays (C₀) (b₀).record (p₀) (p₁) (teller J (P₀)) (T₀) (x₀) ∧
    Release.accepts 505 (p₁).supportExponent (toll J) (S₀).patch.L ∧
    Lute.Plented (C₀) (b₀).record (p₀) (p₁) (S₀).patch.L 505 (x₀)
      (Pert.Asymptotics.regulatorRun R.family z.cutoff z.period (m₀+1)) := by
  apply record_at J Δ extra γ R A z (b₀) (selected J Δ extra γ R paid z)
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  rw [hL]
  exact paid.choose_spec.1 _ _ (step_paid (a₀) (m₀))

theorem cash (hi : Retained.NativeIntake I) (afford : I.inherited≤(a₀).clock.allowance (m₀+1)) :
    ∃ H : Cash (b₀).W (x₀) (b₀).μ (S₀).patch.L (target J (Q₀)) (b₀).order (b₀).c (T₀) (Y₁),
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      ∃ c d v t u b r B q i : ℝ, ∃ k : ℕ,
        (∃ N : ConnectedActivityE6.Blaze.March.Captain H J.outputFieldOrder c d v t u b r B q k Chi.canonical,
          ConnectedActivityE6.Blaze.Silica.Heavy N.conduit) ∧
        ConnectedActivityE6.Blaze.March.Armada (target J (Q₀)) (S₀).patch.L (b₀).μ
          (toll J) (x₀) i B J.outputFieldOrder k := by
  have gate := selected J Δ extra γ R paid z
  have entry := QLocalRequestedSectorIntake.intake R I hi afford
  have hw : Works (teller J (P₀)) (S₀).patch.L (x₀) (S₀) (T₀) :=
    ⟨entry.ready,rfl,by rw [add_comm 1]; exact (a₀).fits.sizeT _ _⟩
  have stamp := PhysicalNext.Repeat.Opera.protocol (n:=z.period) R.alloy.B z.below R.kit.pledging.conducts.full
  obtain ⟨H,renew⟩ := (gate.ledger.2 _ _ _ (T₀) hw).2 stamp (Y₁) entry
  obtain ⟨c,d,v,t,u,b,r,B,q,i,k,capt,army,_⟩ := gate.captain.2 _ _ _ (T₀) hw stamp (Y₁) H
  exact ⟨H,renew,c,d,v,t,u,b,r,B,q,i,k,capt,army⟩

/-- The actual original conditional Cash contains exactly the submitted
    inherited E_i and each compulsory K_i. The two signed prices are relative
    to the same submitted ordinary bill. -/
theorem houses (hi : Retained.NativeIntake I) (afford : I.inherited≤(a₀).clock.allowance (m₀+1)) :
    ∃ H : Cash (b₀).W (x₀) (b₀).μ (S₀).patch.L (target J (Q₀)) (b₀).order (b₀).c (T₀) (Y₁),
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      ∀ (q : Chi) (ε : ℝ), Brim.Houses H (b₀).record q Chi.canonical Chi.canonical ε (p₀) (toll J)
        (wage J R.metals.p R.metals.K (j₁) (j₀)/(S₀).patch.L.val*I.inherited)
        (betaF G (x₀) (S₀).patch.L^γ*I.inherited) := by
  obtain ⟨H,renew,c,d,v,t,u,b,r,B,q',i,k,⟨N,_⟩,_⟩ := cash J Δ extra γ R paid A z I hi afford
  have entry := QLocalRequestedSectorIntake.intake R I hi afford
  have hw : Works (teller J (P₀)) (S₀).patch.L (x₀) (S₀) (T₀) :=
    ⟨entry.ready,rfl,by rw [add_comm 1]; exact (a₀).fits.sizeT _ _⟩
  have recorded := recording J Δ extra γ R paid A z
  have hq : Release.Quotation (C₀) J.outputDistanceOrder 505 (p₁).supportExponent (toll J)
      (wage J R.metals.p R.metals.K (j₁) (j₀)) := by
    rw [(A.input_norm _).reserve]
    exact QLocalInheritedSourcePrice.quote J (C₀) 505
  refine ⟨H,renew,?_⟩
  intro q ε
  exact (selected J Δ extra γ R paid z).glyph (T₀) hw (Y₁) (b₀).μ (b₀).c H (p₀)
    (A.output_norm _).block (A.output_norm _).distance recorded.1 (show 500+5≤505 by decide) recorded.2.1 hq recorded.2.2
    _ le_rfl c d v t u b r B q' k N q ε I.inherited I.error_paid.credit

/-- The complete marked-compatible native sector source including all large
    ordinary and compulsory hard rows. Its signed singleton tariff multiplies
    the actual submitted inherited bill. -/
theorem local_source (hi : Retained.NativeIntake I) (afford : I.inherited≤(a₀).clock.allowance (m₀+1)) :
    ∃ H : Cash (b₀).W (x₀) (b₀).μ (S₀).patch.L (target J (Q₀)) (b₀).order (b₀).c (T₀) (Y₁),
      let matchH : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
      let β := betaF G (x₀) (S₀).patch.L
      Collection.Local (Beam.marquee H (p₀)) (p₀) (Height.serve H matchH Chi.canonical (Beam.lit H))
        (turnFee (p₀)*(Real.exp 1*β^(-(19/16):ℝ)+
          (wage J R.metals.p R.metals.K (j₁) (j₀)/(S₀).patch.L.val*I.inherited + β^γ*I.inherited)))
        (Cash.armK (target J (Q₀)) (S₀).patch.L (b₀).μ (x₀) 0 J.outputFieldOrder) := by
  obtain ⟨H,hrenew,hH⟩ := houses J Δ extra γ R paid A z I hi afford
  have g := selected J Δ extra γ R paid z
  have entry := QLocalRequestedSectorIntake.intake R I hi afford
  have hw : Works (teller J (P₀)) (S₀).patch.L (x₀) (S₀) (T₀) :=
    ⟨entry.ready,rfl,by rw [add_comm 1]; exact (a₀).fits.sizeT _ _⟩
  obtain ⟨c,d,v,t,u,b,r,B,q,k,N,hit⟩ := g.outer (T₀) hw
    (PhysicalNext.Repeat.Opera.protocol (n:=z.period) R.alloy.B z.below R.kit.pledging.conducts.full) (Y₁) H
  let matchH : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
  have reserve : Quotes.preExponent (p₀)=toll J := by
    unfold Quotes.preExponent QLocalRequestedHeirQuote.toll
    rw [(A.output_norm _).reserve]
  exact ⟨H,Beam.shines H (p₀) Chi.canonical matchH rfl rfl rfl rfl hrenew N
    (A.output_norm _).threshold (A.output_norm _).order.le (A.output_norm _).block
    reserve.le (A.output_norm _).distance.le reserve.le hit (hH Chi.canonical (b₀).record.ε)⟩

/-- The original physical Cash may retain its own indexing and compulsory
    field while a matched comparison Cash supplies the regular estimate. -/
def Crossed (book : Booking G) {Y : Rep G (R.family.side (m₀+1) z.period)}
    (H : Cash book.W (x₀) book.μ (S₀).patch.L (target J (Q₀)) book.order book.c (T₀) Y)
    (incoming : ℝ) : Prop :=
  ∀ (Z : Rep G (R.family.side (m₀+1) z.period))
    (C : Cash book.W (x₀) book.μ (S₀).patch.L (target J (Q₀)) book.order book.c (T₀) Z)
    (cross : Match.Alliance C H 1 0), cross.units=Equiv.refl _ → Z.path=Y.path →
      Z.activities.reg=Y.activities.reg → Z.activities.forced=Y.activities.forced →
      let β := betaF G (x₀) (S₀).patch.L
      Collection.Local (Beam.marquee C (p₀)) (p₀) (Height.serve C cross Chi.canonical (Beam.lit C))
        (turnFee (p₀)*(Real.exp 1*β^(-(19/16):ℝ)+
          (wage J R.metals.p R.metals.K (j₁) (j₀)/(S₀).patch.L.val*incoming+β^γ*incoming)))
        (Cash.armK (target J (Q₀)) (S₀).patch.L book.μ (x₀) 0 J.outputFieldOrder)

omit [Fintype V]

theorem source_at_on (book : Booking G)
    (window : QLocalRequestedSectorSale.Window J Δ (Q₀) (C₀) book (S₀).patch (x₀) γ)
    (early : Earlier J R.metals.p R.metals.K extra (j₁) (j₀) (S₀).patch.L.val) (Y : Rep G (R.family.side (m₀+1) z.period))
    (entry : Intake (teller J (P₀)) (T₀) (x₀) Y) (point : Y.p=p₁)
    (beta : Y.beta=(R.family.path.rep z.cutoff z.period (m₀+1)).beta)
    (incoming : ℝ) (old : Y.activities.EBound Y.p incoming) :
    ∃ H : Cash book.W (x₀) book.μ (S₀).patch.L (target J (Q₀)) book.order book.c (T₀) Y,
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧ Crossed J γ R A z book H incoming := by
  have hw : Works (teller J (P₀)) (S₀).patch.L (x₀) (S₀) (T₀) :=
    ⟨entry.ready,rfl,by rw [add_comm 1]; exact (a₀).fits.sizeT _ _⟩
  have stamp := PhysicalNext.Repeat.Opera.protocol (n:=z.period) R.alloy.B z.below R.kit.pledging.conducts.full
  obtain ⟨H,renew⟩ := (window.ledger.2 _ _ _ (T₀) hw).2 stamp Y entry
  obtain ⟨c,d,v,t,u,b,r,B,q,k,N,hit⟩ := window.outer (T₀) hw stamp Y H
  have recorded := record_at J Δ extra γ R A z book window early
  have plays : Plays (C₀) book.record (p₀) Y.p (teller J (P₀)) (T₀) (x₀) := point.symm ▸ recorded.1
  have accepts : Release.accepts 505 Y.p.supportExponent (toll J) (S₀).patch.L := point.symm ▸ recorded.2.1
  have quote : Release.Quotation (C₀) J.outputDistanceOrder 505 Y.p.supportExponent (toll J)
      (wage J R.metals.p R.metals.K (j₁) (j₀)) := by
    rw [point,(A.input_norm _).reserve]
    exact QLocalInheritedSourcePrice.quote J (C₀) 505
  have plented : Lute.Plented (C₀) book.record (p₀) Y.p (S₀).patch.L 505 (x₀) (ConnectedActivityE6.Coat.gStep Y.beta) := by
    rw [point,beta]
    exact recorded.2.2
  have houses := window.glyph (T₀) hw Y book.μ book.c H (p₀) (A.output_norm _).block
    (A.output_norm _).distance plays (show 500+5≤505 by decide) accepts quote plented _ le_rfl c d v t u b r B q k N
    Chi.canonical book.record.ε incoming old
  have reserve : Quotes.preExponent (p₀)=toll J := by
    unfold Quotes.preExponent QLocalRequestedHeirQuote.toll
    rw [(A.output_norm _).reserve]
  refine ⟨H,renew,?_⟩
  intro Z C cross hu hp hr hk
  exact Beam.shines C (p₀) Chi.canonical cross hu hp hr hk renew N
    (A.output_norm _).threshold (A.output_norm _).order.le (A.output_norm _).block
    reserve.le (A.output_norm _).distance.le reserve.le hit houses

theorem source_at (book : Booking G)
    (window : QLocalRequestedSectorSale.Window J Δ (Q₀) (C₀) book (S₀).patch (x₀) γ)
    (early : Earlier J R.metals.p R.metals.K extra (j₁) (j₀) (S₀).patch.L.val) (Y : Rep G (R.family.side (m₀+1) z.period))
    (entry : Intake (teller J (P₀)) (T₀) (x₀) Y) (point : Y.p=p₁)
    (beta : Y.beta=(R.family.path.rep z.cutoff z.period (m₀+1)).beta)
    (incoming : ℝ) (old : Y.activities.EBound Y.p incoming) :
    ∃ H : Cash book.W (x₀) book.μ (S₀).patch.L (target J (Q₀)) book.order book.c (T₀) Y,
      let matchH : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
      let β := betaF G (x₀) (S₀).patch.L
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      Collection.Local (Beam.marquee H (p₀)) (p₀) (Height.serve H matchH Chi.canonical (Beam.lit H))
        (turnFee (p₀)*(Real.exp 1*β^(-(19/16):ℝ)+
          (wage J R.metals.p R.metals.K (j₁) (j₀)/(S₀).patch.L.val*incoming+β^γ*incoming)))
        (Cash.armK (target J (Q₀)) (S₀).patch.L book.μ (x₀) 0 J.outputFieldOrder) := by
  obtain ⟨H,renew,source⟩ := source_at_on J Δ extra γ R A z book window early Y entry point beta incoming old
  exact ⟨H,renew,source Y H (Match.staple rfl rfl rfl) rfl rfl rfl rfl⟩

theorem source_for_on (Y : Rep G (R.family.side (m₀+1) z.period))
    (entry : Intake (teller J (P₀)) (T₀) (x₀) Y) (point : Y.p=p₁)
    (beta : Y.beta=(R.family.path.rep z.cutoff z.period (m₀+1)).beta)
    (incoming : ℝ) (old : Y.activities.EBound Y.p incoming) :
    ∃ H : Cash (b₀).W (x₀) (b₀).μ (S₀).patch.L (target J (Q₀)) (b₀).order (b₀).c (T₀) Y,
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧ Crossed J γ R A z (b₀) H incoming := by
  apply source_at_on J Δ extra γ R A z (b₀) (selected J Δ extra γ R paid z) _ Y entry point beta incoming old
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  rw [hL]
  exact paid.choose_spec.1 _ _ (step_paid (a₀) (m₀))

theorem source_for (Y : Rep G (R.family.side (m₀+1) z.period))
    (entry : Intake (teller J (P₀)) (T₀) (x₀) Y) (point : Y.p=p₁)
    (beta : Y.beta=(R.family.path.rep z.cutoff z.period (m₀+1)).beta)
    (incoming : ℝ) (old : Y.activities.EBound Y.p incoming) :
    ∃ H : Cash (b₀).W (x₀) (b₀).μ (S₀).patch.L (target J (Q₀)) (b₀).order (b₀).c (T₀) Y,
      let matchH : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
      let β := betaF G (x₀) (S₀).patch.L
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      Collection.Local (Beam.marquee H (p₀)) (p₀) (Height.serve H matchH Chi.canonical (Beam.lit H))
        (turnFee (p₀)*(Real.exp 1*β^(-(19/16):ℝ)+
          (wage J R.metals.p R.metals.K (j₁) (j₀)/(S₀).patch.L.val*incoming+β^γ*incoming)))
        (Cash.armK (target J (Q₀)) (S₀).patch.L (b₀).μ (x₀) 0 J.outputFieldOrder) := by
  apply source_at J Δ extra γ R A z (b₀) (selected J Δ extra γ R paid z) _ Y entry point beta incoming old
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  rw [hL]
  exact paid.choose_spec.1 _ _ (step_paid (a₀) (m₀))

end YM.Integration.QLocalRequestedSectorCalendar
end
