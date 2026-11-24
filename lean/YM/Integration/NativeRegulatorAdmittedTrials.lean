import YM.Integration.NativeFundedRegulatorCollector
import YM.Integration.NativeRegulatorInitialDatum
import YM.Integration.NativeRegulatorLocalMeasurement

/-! Fund each finite regulator horizon together with any prescribed physical
period and starting level on the same actual family of converging cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeRegulatorAdmittedTrials

open Function Filter Lattice Labels Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.Verne FVA2.ColorCode
open FormalOPE.RG10.Position
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalRegulatorCollector NativeFormalDiagonalCollector
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple}

theorem level {W : Bank R hG} {μ : ℝ} {P : Prescription (nativeDeck R)}
    {Z : branches R} {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
    {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
    (T : Trial W μ P Z C A g i S) (j : ℕ) : T.order ≤ NativeRegulatorInitialDatum.level T j := by
  let s := schedule Z C T.order j
  let b := Lodge.acquire (program R) Z s (R.family.path.levels.clock.factor s)
  let N := C.whereAt (program R) Z R s (above Z C T.order j)
  have hb : T.order < b := by unfold b Lodge.acquire s schedule; omega
  have hb0 : 0 < b := (Nat.zero_le _).trans_lt hb
  have hmul : b ≤ b*b := Nat.le_mul_of_pos_right _ hb0
  have hs : 2*(b*b) ≤ N := C.has_space (program R) Z R s (above Z C T.order j)
  change T.order ≤ N-1
  omega

variable (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
  (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
  (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R)

/-- One finite demand pays a common lower bound before choosing its stop and
retains original finite normalized coefficients for all its fields and tests. -/
theorem finite (g : G.ColorIndex) {I : Type} [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I)
    (buy : ∀ p : ℕ, 0 < p → NativeFormalComplexCollector.Converges W μ J X P Z C A p g)
    (s : Finset (Request R.family.labels)) (q : ℕ) :
    ∃ T : Trial W μ P Z C A g i S, q+1 ≤ T.order ∧
      T.order ≤ (R.family.S.period (T.stop T.station)).val ∧
      ∀ a ∈ s, dist (NativeRegulatorLocalMeasurement.measure T a) (target W μ J X a) < 1/(q+1:ℝ) := by
  let p := q + 1 + ∑ a ∈ s, a.order
  have hq : q+1 ≤ p := Nat.le_add_right _ _
  have hp : 0 < p := (Nat.zero_lt_succ q).trans_le hq
  obtain ⟨F,x,_,funds,walk,_⟩ := buy p hp
  obtain ⟨Λ,hΛ⟩ := funds.fees
  let stop (j : ℕ) := max (Λ j) p
  have walk' : Supplier.Walk (program R) Z R C (schedule Z C p) (above Z C p) μ P p atTop x F stop :=
    ⟨walk.region,hΛ stop (Eventually.of_forall fun _ => le_max_left ..)⟩
  obtain ⟨⟨B⟩,reads⟩ := funds.reach x stop walk' I inferInstance inferInstance i S
  let T (j : ℕ) : Trial W μ P Z C A g i S := ⟨p,j,F,x,stop,B,funds,walk'⟩
  have horder (a : s) : a.val.order ≤ p := by
    have he := Finset.single_le_sum (f := Request.order) (fun b _ => Nat.zero_le b.order) a.property
    dsimp only [p]
    omega
  have hnear (a : s) : ∀ᶠ j in atTop, dist (NativeRegulatorLocalMeasurement.measure (T j) a.val)
      (target W μ J X a.val) < 1/(q+1:ℝ) := by
    have hread v := reads B a.val.horizon v
    have hc : Tendsto (fun j => (T j).measure a.val) atTop (𝓝 (target W μ J X a.val)) := by
      refine NativeFormalComplexCollector.limits_fields W μ J X _ (fun v => ?_) _ (horder a) _ _
      rw [readout, NativeFormalFieldTransition.regulated W μ J X a.val.horizon v]
      exact hread v
    have hl := hc.congr' (Eventually.of_forall fun j => NativeRegulatorLocalMeasurement.measure_eq (T j) a.val)
    exact Metric.tendsto_nhds.mp hl _ (by positivity)
  obtain ⟨j,hj⟩ := (Filter.eventually_all.2 hnear).exists
  refine ⟨T j,hq,?_,fun a ha => hj ⟨a,ha⟩⟩
  exact (le_max_right (Λ j) p).trans (R.family.S.period_strict.id_le (stop j))

def Cofinal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I) (g : G.ColorIndex),
    ∃ T : Demand R.family.labels → Trial W μ P Z C A g i S,
      (∀ z, z.2+1 ≤ (T z).order) ∧
      (∀ z, (T z).order ≤ (R.family.S.period ((T z).stop (T z).station)).val) ∧
      (∀ z j, (T z).order ≤ NativeRegulatorInitialDatum.level (T z) j) ∧
      Tendsto (fun z => (T z).cutoff) atTop atTop ∧
      ∀ a : Request R.family.labels, Tendsto (fun z => NativeRegulatorLocalMeasurement.measure (T z) a)
        atTop (𝓝 (target W μ J X a))

theorem all_tests (buy : ∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex,
    NativeFormalComplexCollector.Converges W μ J X P Z C A p g) : Cofinal W μ J X P Z C A := by
  intro I _ _ i S g
  choose T hT period near using fun z : Demand R.family.labels =>
    finite W μ J X P Z C A g i S (fun p hp => buy p hp g) z.1 z.2
  refine ⟨T,hT,period,fun z j => level (T z) j,?_,?_⟩
  · apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop ((∅,b) : Demand R.family.labels)).mono fun z hz =>
      hz.2.trans ((Nat.le_succ z.2).trans ((hT z).trans (T z).order_le))
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ q : ℕ in atTop, 1/(q+1:ℝ) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hε)
  obtain ⟨b,hb⟩ := eventually_atTop.1 hsmall
  exact (eventually_ge_atTop (({a},b) : Demand R.family.labels)).mono fun z hz =>
    (near z a (hz.1 (Finset.mem_singleton_self a))).trans (hb z.2 hz.2)

/-- Every specified originally funded economy keeps its own calibrated
fields while increasing the actual physical period for all numerator terms. -/
theorem funded (P : Prescription (wings G)) (H : NativeFundedRegulatorCollector.Realizes W μ P J X) :
    ∃ (Z : branches R) (C : Lodge.Contract R (program R) Z) (D : Drivers)
      (L : Patience (Study.Plan R) D) (A : table R),
      YM.FVAAlt2.Mass.Framed (Study.Plan R) L A ∧
      Cofinal W μ J X (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) Z C A := by
  obtain ⟨_,_,_,Z,C,D,L,A,hA,buy,_,_⟩ := H
  exact ⟨Z,C,D,L,A,hA,all_tests W μ J X _ Z C A buy⟩

end YM.Integration.NativeRegulatorAdmittedTrials
end
