import YM.Integration.WilsonRegisteredIntakeNorm
import YM.Integration.WilsonCoherentMayerOldSlots

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredActionOccurrence
open Filter Lattice RG Pressure Tree Wilson Work.E03 RGLocalTaylor RGLocalTaylor.Insert
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}

private theorem real_restrict {n:Side} {P Q:BudgetPoint} (threshold:Q.threshold=P.threshold)
    (order:Q.order≤P.order) (power:Q.power≤P.power)
    {S:Support n} {o:Site n} {f:Config G n→ℝ} {c:ℝ}
    (reg:P.Regular S f) (income:P.supBounds o S f c) :
    Q.Regular S f ∧ Q.supBounds o S f c:=by
  refine ⟨⟨reg.sites,reg.borel,reg.symmetry,?_,?_⟩,income.1,?_⟩
  · intro U health
    rw [threshold] at health
    exact (reg.smooth U health).of_le (by exact_mod_cast order)
  · intro U health A l short
    rw [threshold] at health
    exact reg.hasDerivs U health A l (short.trans_le order)
  · intro U health l size directions
    rw [threshold] at health
    apply income.2 U health l (size.trans order)
    intro a member e
    have original:=directions a member e
    rw [threshold] at original
    exact original.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) power) P.threshold_pos.le)

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus Progress.DirectedRecipe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical



/-- Vary one actual old action occurrence, retaining the whole compatible prior at that field. -/
def tilt {f:Side} (P:Rep G f) (i:ℕ) (s:ℝ) (U:Config G f):ℝ :=
  Real.exp (P.exponent U-s*P.activities.regularOccurrence P.p i U)*P.activities.gas P.p U

theorem income {f:Side} (P:Rep G f) (i:ℕ) (U:Config G f):
    tilt P i 0 U=P.eval U ∧ HasDerivAt (fun s=>tilt P i s U)
      (P.eval U*(-P.activities.regularOccurrence P.p i U)) 0 := by
  constructor
  · simp [tilt,Rep.eval]
  let h:=P.activities.regularOccurrence P.p i U
  have de : HasDerivAt (fun s : ℝ=>P.exponent U-s*h) (-h) 0 := by
    have lin : HasDerivAt (fun t:ℝ=>t*h) h 0 := by
      simpa only [one_mul] using (hasDerivAt_id' (0:ℝ)).mul_const h
    exact lin.const_sub (P.exponent U)
  have receipt:=de.exp.mul_const (P.activities.gas P.p U)
  unfold tilt
  simpa only [h,Rep.eval,zero_mul,sub_zero,mul_comm,mul_left_comm,mul_assoc] using receipt

theorem registered (R:Run G) {k N per f p:ℕ} {s:ℝ} (live:k≤N)
    (onset:R.family.ref (max f p)≤k) (Q:Rep G (R.family.side k per))
    (record:LocalComparison.NormAt R.family k Q.p f p s):
    let P:=R.family.path.rep N per k
    ∃e:ℕ→ℝ,(∀z,SumBudget (fun i=>if (P.activities.reg i).site=z then P.p.mass (P.activities.reg i).support (e i) else 0)
      (R.family.path.levels.clock.allowance k)) ∧
    ∀i (old:Team (QLocalInheritedRegularSlots.carrier Q)),
      ∃(W:Team (QLocalInheritedRegularSlots.carrier Q))(b:Leaf (QLocalInheritedRegularSlots.carrier Q)),
        old.own⊆W.own ∧ b∈W.own ∧ W.weight=old.weight*e i ∧ b.crest=(P.activities.reg i).support ∧
        (P.activities.reg i).site∈b.crest ∧ ∀U,
          b.ingredient U=P.activities.regularOccurrence P.p i U ∧
          HasDerivAt (fun t=>tilt P i t U) (P.eval U*(-b.ingredient U)) 0 := by
  classical
  intro P
  have good:=(R.makes.wilson.represents N per k live).good.labels
  obtain ⟨e,caps,roots⟩:=good.boundE
  refine ⟨e,roots,?_⟩
  intro i old
  let addr:=P.activities.reg i
  obtain ⟨threshold,_,order,power⟩:=WilsonRegisteredIntakeNorm.dated R (per:=per) live onset Q.p record
  obtain ⟨reg,cost⟩:=real_restrict threshold order power (good.regular.smooth i) (caps i)
  obtain ⟨t,fresh⟩:=WilsonCoherentMayerOldSlots.room Q addr old
  let b:=ManuscriptQLocalOrdinaryLeaf.leaf Q addr (P.activities.E i) reg cost t
  let W:=WilsonCoherentMayerOldSlots.booked Q addr old t fresh (P.activities.E i) reg cost
  have bought:=WilsonCoherentMayerOldSlots.entered Q addr old t fresh (P.activities.E i) reg cost
  refine ⟨W,b,bought.2.1,bought.1,bought.2.2.1,bought.2.2.2.1,bought.2.2.2.1.symm ▸ addr.anchor,?_⟩
  intro U
  have read : b.ingredient U=P.activities.regularOccurrence P.p i U:=by
    rw [bought.2.2.2.2 U,threshold]
    rfl
  exact ⟨read,read.symm ▸ (income P i U).2⟩

end YM.Integration.WilsonRegisteredActionOccurrence
