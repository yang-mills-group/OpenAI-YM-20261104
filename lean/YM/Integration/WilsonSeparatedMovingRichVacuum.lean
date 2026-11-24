import YM.Integration.WilsonSeparatedMovingRichCluster
import YM.Integration.WilsonReportMomentEnvelope

/-! The true measurement of the (physical) unit with a moving eligible
far probe is uniformly bounded on the whole original prescribed support.
Both field slots and the normalization here use the same reporting clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingRichVacuum
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Filter Set MeasureTheory Lattice Extraction Table Spec Climb OPE OPE.Orbits RG17 SharpGram PhysMS
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid IntrinsicWilsonTensor ContinuumIntrinsicWilsonProduct
open WilsonSeparatedMovingRichGeometry PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book}

def lower {C:Family G} {D n m:ℕ} (P:Plan C D n m) : Plan C 0 n m where
  b:=P.b
  middle:=P.middle
  j:=P.j
  h:=P.h
  a:=P.a
  c:=P.c
  coarse:=P.coarse
  mid:=P.mid
  fine:=P.fine
  pos:=P.pos
  before:=P.before
  low:=P.low
  high:=P.high
  margin:=by
    have h:=P.margin
    have reduce:(D:ℝ)*(P.a-P.h)≤D := mul_le_of_le_one_right (Nat.cast_nonneg D) (by linarith only [P.low,P.pos])
    dsimp only [FilteredIntrinsicGramReadout.Margin] at h ⊢
    push_cast
    nlinarith only [h,reduce]

def fields (B:Deck G) (D:ℕ) (b:Glyph B D) (J:ℝ→tower V) (τ:ℝ) : Labels V (fun _:Fin 1=>D) :=
  fun _=>J τ D (WilsonMacroscopicRichFree.basis R.family B D b)

private def degrees (D:ℕ) : Caps 2 := Fin.cons (α:=fun _:Fin 2=>ℕ) 0 (fun _:Fin 1=>D)

private def unitTrain (B:Deck G) (D:ℕ) (b:Glyph B D) : (i:Fin 2)→Input R.family ((degrees D) i) :=
  Fin.cons (α:=fun i:Fin 2=>Input R.family (degrees D i)) ((Bel R.family.book).unit 0) (fun _=>WilsonMacroscopicRichFree.basis R.family B D b)

theorem equal (B:Deck G) (F : Final R.family f V) (J:ℝ→tower V) (D:ℕ) (φ:Test 2) {τ:ℝ} (tp:0<τ)
    (unit:J τ 0 ((Bel R.family.book).unit 0)=V.unit 0) (b:Glyph B D) (x:Points 2) (safe:x∈conf 2) :
    upon V 0 0 (far τ x) (fields B D b J τ) (V.unit 0)=
      V.classMoment V (degrees D) (τ • x) (Frame.born J τ (unitTrain B D b)) := by
  let X:=WilsonMacroscopicRichRegister.exterior B J φ tp b
  have offset : X.offset (τ • x)=far τ x := by funext i;change τ • x i.succ-τ • x 0=τ • (x i.succ-x 0);rw [smul_sub]
  rw [←offset]
  have law:=X.pay_eq F 0 (V.unit 0) (τ • x) (Work.A05.smul_conf tp safe)
  apply law.trans
  let u:=(Frame.born J τ (unitTrain B D b))
  have tags : Fin.cons (α:=fun _ : Fin 2=>V.Tag) ⟨0,V.unit 0⟩ X.tags=
      fun i=>⟨(degrees D) i,u i⟩ := by
    funext i;fin_cases i
    · change (⟨0,V.unit 0⟩:V.Tag)=⟨0,J τ 0 ((Bel R.family.book).unit 0)⟩
      rw [unit]
    · rfl
  exact congrArg (V.useAt V (τ • x)) tags

theorem original (B:Deck G) (F : Final R.family f V) (J:ℝ→tower V) (lead:Leading F J) (D:ℕ) (φ:Test 2)
    {A:(Bel R.family.book).Hierarchy} (paid:∀ d:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) d) :
    ∃ L:ℝ,0≤L ∧ ∀ᶠ τ in trail,∀ b:Glyph B D,∀ x∈tsupport φ,
      ‖upon V 0 0 (far τ x) (fields B D b J τ) (V.unit 0)‖≤L := by
  obtain ⟨M,M0,envelope⟩:=WilsonReportMomentEnvelope.purchased F J lead paid (degrees D)
    (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  let fee (b:Glyph B D):=M*∏i,‖unitTrain (R:=R) B D b i‖
  have fp (b:Glyph B D):0≤fee b := mul_nonneg M0.le (Finset.prod_nonneg fun _ _=>norm_nonneg _)
  refine ⟨∑b,fee b,Finset.sum_nonneg (fun b _=>fp b),?_⟩
  filter_upwards [envelope,lead.unit 0,length_rate.pos] with τ source unit tp b x hx
  change 0<τ at tp
  rw [equal B F J D φ tp unit b x (φ.tsupport_subset hx)]
  exact (source x hx (unitTrain B D b)).trans (Finset.single_le_sum (fun c _=>fp c) (Finset.mem_univ b))

end YM.Integration.WilsonSeparatedMovingRichVacuum
