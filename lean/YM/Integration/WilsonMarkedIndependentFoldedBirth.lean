import YM.Integration.WilsonRegisteredBareMarkedWinding
import YM.Integration.WilsonMarkedIndependentFoldedIntegral
import YM.Integration.WilsonRegisteredPointWindingReadout

/-! The folded finite one-source program on its original nonbare date. Before
the native kinetic reversion it is the normalized affine insertion of the
literal enrolled source on the fine torus, with the folded upper vacuum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentFoldedBirth
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}

private theorem oneHeat {U:Type}(P:thalamus D U)(s:ι):turnTLog P {s}=P {s}:=by
  rw [turnTLog,dif_neg (Finset.singleton_ne_empty s)]
  have dropped:∀J∈({s}:Finset ι).powerset,
      (if h:J⊆{s}∧J≠{s} then (J.card:ℝ) • foamT h.1 (turnTLog P J) (P ({s}\J)) else 0)=0:=by
    intro J _
    split
    next h=>
      have eq:J=∅:=Finset.card_eq_zero.mp (by simpa using Finset.card_lt_card (lt_of_le_of_ne h.1 h.2))
      subst J
      simp
    next h=>rfl
  rw [sum_eq_zero dropped,smul_zero,sub_zero]

omit [DecidableEq ι] in
private theorem empty {K:family G D}(h:K ∅=0):(repaint K) ∅=0:=by
  rw [repaint,h]
  apply Prod.ext
  · funext n e r
    exact plume_zero n
  · rfl

/-- Every incoming marked tensor belongs to the same original polynomial.
The before-reset finite integrand is the genuine folded quiet Wick insertion
at this date. -/
theorem singleton (A:Levels G)(O:ChartRatio G)(m N:ℕ)(n:Side)(s:ι)(E:family G D)
    (ex:Eu k E)(vac:E ∅=0)(C:Cost):
    let L:=loose A m
    let f:=n*L.L
    coilH A O m N n E k C {s}=Blue.mix C
      (reed (stepAt L A.clock.kernel n) (xree L A.clock.kernel n) (freeForms A N (m+1))
        (roam A N m n) O (emera (actionW A O N (m+1)) f) (mass k {s}) (((repaint E) {s}).1 f)):=by
  intro L f
  unfold coilH WilsonCoeffUV.Wheel.Mark.mist inHeat
  simp only [oneHeat]
  unfold oven
  rw [levSingle (empty vac) (repose ex) s]
  rfl

variable [Fintype ι]{I:ι→Type}[∀i,Fintype (I i)]

/-- The single freshly declared source on a nonbare history requires no
difference between two old finite quiet recursions. Its actual charged raw
polynomial on the finite torus is the entering insertion. -/
theorem original (A:Levels G)(O:ChartRatio G)(m N:ℕ)(n:Side)(s:ι)(X:∀i,I i→Seed G (D i))
    (h:∀i b,(X i b).rank≤k i+(X i b).head)(z:ι → Cover)(C:Cost):
    let L:=loose A m
    let f:=n*L.L
    let E:=independent X z
    coilH A O m N n E k C {s}=Blue.mix C
      (reed (stepAt L A.clock.kernel n) (xree L A.clock.kernel n) (freeForms A N (m+1))
        (roam A N m n) O (emera (actionW A O N (m+1)) f) (mass k {s}) ((E {s}).1 f)):=by
  intro L f E
  obtain ⟨_,legal,hush,_⟩:=IndependentSourcePathFamily.preblock X (k:=k) z ({s}) 0 (w:=1) zero_lt_one h
  rw [singleton A O m N n s E legal hush C]
  have same:((repaint E) {s}).1 f=(E {s}).1 f:=by
    funext j r
    exact (WilsonRegisteredBareMarkedWinding.original X z h {s} f j r).symm
  rw [same]

end YM.Integration.WilsonMarkedIndependentFoldedBirth
end
