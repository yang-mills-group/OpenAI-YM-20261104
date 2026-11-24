import YM.Integration.WilsonMovingExternalFields
import YM.Integration.WilsonMacroscopicPointPacket

/-! A full-product point detector on one actual finite regulator. Rounding
is only the original right-closed mesh; the external test is integrated on
its originally assigned coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegulatorPointDetector
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S} {n:ℕ}

def reading (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex)
    (z:Points (n+X.n)):ℂ:=WilsonMovingExternalFields.physical R L X d w r i (address (R.family.S.a i.1) z)

def measured (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex)
    (x:Points n):ℂ:=∫u:Points (X.n+1),X.test u*reading R L X d w r i (absCord n X.n r (x,u))

def incoming (L:Layout F) (h:ℕ) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex) (x:Points n):S.Field h:=
    WilsonMacroscopicDetector.restore F h fun Y:WilsonMacroscopicDetector.probes F h=>measured R L Y.val d w r i x

private theorem addressable (N n:ℕ):Measurable (address (R.family.S.a N) :Points n→(Fin n → Cover)):=by
  apply measurable_to_countable;intro z;exact measurable_segment (R.family.S.a_pos N) (address (R.family.S.a N) z)

theorem measurable (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex):
    Measurable (reading R L X d w r i):=(measurable_of_countable _).comp (addressable R i.1 _)

theorem finite (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex):
    let tags:=Fin.append (fun j=>(⟨d j,atRef L (d j) r i (w j)⟩:R.family.book.Token)) (refTags X)
    ∀z:Points (n+X.n),‖reading R L X d w r i z‖ ≤ ∑a:Var R.family.S (n+X.n) i.1 i.2,‖R.family.numeric i.1 i.2 tags a‖:=by
  intro tags z;exact Finset.single_le_sum (fun a _=>norm_nonneg _) (Finset.mem_univ (wrap _ ∘ address (R.family.S.a i.1) z))

theorem integrable (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex) (x:Points n):
    Integrable (fun u:Points (X.n+1)=>X.test u*reading R L X d w r i (absCord n X.n r (x,u))):=by
  have obs:Measurable (fun u:Points (X.n+1)=>reading R L X d w r i (absCord n X.n r (x,u))):=
    (measurable R L X d w r i).comp ((absCord_cont r).comp (continuous_const.prodMk continuous_id)).measurable
  have tested:Integrable (fun u:Points (X.n+1)=>X.test u):=X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport
  let tags:=Fin.append (fun j=>(⟨d j,atRef L (d j) r i (w j)⟩:R.family.book.Token)) (refTags X)
  let B:=∑a:Var R.family.S (n+X.n) i.1 i.2,‖R.family.numeric i.1 i.2 tags a‖
  apply (tested.norm.mul_const B).mono' (X.test.continuous.measurable.mul obs).aestronglyMeasurable
  filter_upwards with u
  change ‖X.test u*reading R L X d w r i (absCord n X.n r (x,u))‖ ≤ ‖X.test u‖*B
  rw [norm_mul];exact mul_le_mul_of_nonneg_left (finite R L X d w r i _) (norm_nonneg _)

theorem measurable_read (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex):
    Measurable (measured R L X d w r i):=by
  let T (p:Points n×Points (X.n+1)):=X.test p.2*reading R L X d w r i (absCord n X.n r p)
  have ht:Measurable T:=(X.test.continuous.measurable.comp measurable_snd).mul ((measurable R L X d w r i).comp (absCord_cont r).measurable)
  exact ht.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_incoming (L:Layout F) (h:ℕ) (d:Caps n) (w:R.family.book.Vector d) (r:ℝ) (i:UVIndex):
    StronglyMeasurable (incoming R L h d w r i):=(WilsonMacroscopicDetector.restore F h).continuous.stronglyMeasurable.comp_measurable
      (measurable_pi_lambda _ (fun Y:WilsonMacroscopicDetector.probes F h=>measurable_read R L Y.val d w r i))

end YM.Integration.WilsonRegulatorPointDetector
