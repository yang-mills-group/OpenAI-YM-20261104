import YM.Integration.WilsonMacroscopicRichPrescribedGridBudget
import YM.Integration.WilsonRootedOPEPointFloor

/-! On the genuine compact angles the full independently prescribed local
Wilson operand is bounded by the very point normalization already bought. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichGridCofactors
open Filter Function Finset Lattice Wilson RG Marker Source Labels MeasureTheory
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open RGComparison.Core16 MS.Menus MS.Rake MS.Local
open scoped BigOperators Classical
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{B:Physical.Deck G}(R:Run G)(v:V→Label B)
omit [DecidableEq V] [Fintype V] in
private theorem compact (i:V)(a:Glyph B (v i).h):
    ∃c:ℝ,0≤c ∧ ∀(N p:ℕ)(x:Site (R.family.side N p))(U:Config G (R.family.side N p)),
      ‖R.family.O N p (WilsonMacroscopicRichOriginalPortfolio.label R N p a) x U‖≤c:=by
  obtain ⟨b,bd⟩:=(Envelope.compactC ((R.family.localSection a.size).continuous_evaluate
    (ActualOriginalDictionary.coordinates R B a.size a.grade a.2.2))).cost
  refine ⟨max 0 b,le_max_left ..,?_⟩
  intro N p x U
  rw [WilsonMacroscopicRichOriginalPortfolio.label,Descent.field_label_correct]
  exact (bd _).trans (le_max_right ..)

theorem purchased :
    ∃C:ℝ,1≤C ∧ ∀(hG:G.Simple)(J:Request V)(A:NumericSchedule R.family J)
      (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)(μ:ℝ)(ord:V→ℕ)
      (x:V→Site (R.family.side (d.level+1) d.period))(i:V)(U:Config G (R.family.side (d.level+1) d.period)),
      ‖WilsonMacroscopicRichOriginalPortfolio.observation R Q (d.level+1) d.period (v i)
        (μ-R.family.S.scale d.cutoff) (ord i) (x i) U‖≤C*WilsonMacroscopicRichGridUnit.fee R hG v J A d Q μ ord x:=by
  choose b bp bound using compact R v
  let reciprocal (z:Slot v):=(WilsonRootedOPEGlyph.mass R v (WilsonRootedOPEGlyph.row R v z))⁻¹
  have rp (z:Slot v):0≤reciprocal z:=inv_nonneg.mpr (WilsonRootedOPEGlyph.acquired R v z).2.le
  let sum (i:V):=∑a:Glyph B (v i).h,reciprocal ⟨i,a⟩*b i a
  have positive (i:V):0 ≤ sum i:=sum_nonneg fun a _=>mul_nonneg (rp _) (bp i a)
  let C:=max 1 (∑i:V,sum i)
  refine ⟨C,le_max_left ..,?_⟩
  intro hG J A d Q μ ord x i U
  let M:=WilsonMacroscopicRichGridUnit.fee R hG v J A d Q μ ord x
  have mp:0<M:=zero_lt_one.trans_le (le_max_left ..)
  have fees (a:Glyph B (v i).h):‖oil (Q.fees (v i).h (v i).item) a (ord i) (μ-R.family.S.scale d.cutoff)‖≤reciprocal ⟨i,a⟩*M:=by
    have check:=WilsonRootedOPEPointFloor.funded R v x (fun j=>(J.tests j).D) (fun _=>0) Q μ ord
      ((ActualOriginalQInitialInput.schedule R hG v J A).input_width_pos d.level).le d.cutoff ⟨i,a⟩
    exact (div_le_iff₀ mp).mp check
  calc
    _ ≤ ∑a:Glyph B (v i).h,‖oil (Q.fees (v i).h (v i).item) a (ord i) (μ-R.family.S.scale d.cutoff)*
      R.family.O (d.level+1) d.period (WilsonMacroscopicRichOriginalPortfolio.label R (d.level+1) d.period a) (x i) U‖:=norm_sum_le _ _
    _ ≤ ∑a:Glyph B (v i).h,(reciprocal ⟨i,a⟩*b i a)*M:=by
      apply sum_le_sum;intro a _
      rw [norm_mul]
      exact (mul_le_mul (fees a) (bound i a _ _ _ _) (norm_nonneg _) (mul_nonneg (rp _) mp.le)).trans_eq (by ring)
    _=sum i*M:=(Finset.sum_mul ..).symm
    _≤C*M:=mul_le_mul_of_nonneg_right ((single_le_sum (fun j _=>positive j) (mem_univ i)).trans (le_max_right 1 _)) mp.le

end YM.Integration.WilsonMacroscopicRichGridCofactors
