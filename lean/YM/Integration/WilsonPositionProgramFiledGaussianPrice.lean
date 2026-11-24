import YM.Integration.WilsonPositionProgramGaussianEnvelope
import YM.Integration.WilsonPositionProgramQuietDriver

/-! One signed cofactor per change, priced from the original finite Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiledGaussianPrice
open Function Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange Next.SectorChange.Gaussian PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open WilsonPositionProgramGaussianRoute WilsonPositionProgramGaussianEnvelope WilsonPositionProgramFiledGaussianChange
open scoped BigOperators Classical
section weights
variable {I V:Type} [DecidableEq V] [Fintype V] [DecidableEq I] [Fintype I] {R:Census V}
  (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℝ)
  (p q:Hot R→Normal.poly I)(s:R.Mode)(anchor:I→ℝ)
  (e:Hot R→ℝ)(E:Hot R→Normal.poly I)

def expense : List (Hot R) → ℝ
  | [] => 0
  | i::rest =>
      let old:=staged p q rest
      let co:=WilsonPositionProgramGaussianDriver.hearing Q hQ (Cloud.shift m) old s i
      e i * (Cloud.wick Q hQ (Cloud.shift m) (stock (E i) co)).re+expense rest

omit [Fintype V] in
theorem priced (hq:Q.PosSemidef)
    (submit:∀i z,‖Cloud.paint (m+z) (anchored s anchor i (q i-p i))‖
        ≤e i*(Cloud.paint (m+z) (E i)).re)(book:List (Hot R))(nd:book.Nodup):
    ‖Cloud.wick Q hQ (Cloud.shift m) (tally Q hQ (Cloud.shift m) p q s anchor book)‖
      ≤expense Q hQ m p q s e E book:=by
  induction book with
  | nil=>simp only [tally,map_zero,norm_zero,expense,le_refl]
  | cons i rest ih=>
    let co:=WilsonPositionProgramGaussianDriver.hearing Q hQ (Cloud.shift m) (staged p q rest) s i
    have seen:staged p q rest i=p i:=by simp [staged,(List.nodup_cons.mp nd).1]
    have hay:=bound Q hQ hq m (anchored s anchor i (q i-p i)) co (E i) (e i) (submit i)
    rw [tally,map_add,expense,seen]
    exact (norm_add_le _ _).trans (add_le_add hay (ih (List.nodup_cons.mp nd).2))

end weights
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

theorem original (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){d r:ℕ}(retained:d≤r)
    (s:R.Mode)(live:s≠R.quiet)(anchor:Precision.Key F G→ℝ)
    (e:Hot (Board R r)→ℝ)(E:Hot (Board R r)→Normal.poly (Precision.Key F G))
    (submit:∀i z,‖Cloud.paint z (anchored (Join.pair s (pick r d)) anchor i
       (drivers K F tag Y A r i-drivers K F tag W A r i))‖≤e i*(Cloud.paint z (E i)).re):
    ‖(d.factorial:ℂ)*((observe R r (logMarked (Bulk.Fk K F tag Y A r)) d).part s-
      (observe R r (logMarked (Bulk.Fk K F tag W A r)) d).part s)‖
    ≤expense (K.covariance F tag) (K.symm F tag) 0 (drivers K F tag W A r) (drivers K F tag Y A r)
      (Join.pair s (pick r d)) e E Finset.univ.toList:=by
  rw [WilsonPositionProgramFiledGaussianChange.original K F tag W Y A retained s live anchor]
  have cash:=Cloud.paid (K.covariance F tag) (K.symm F tag) (K.positive F tag).posSemidef
    0 (cofactor K F tag W Y A r d s anchor)
  simp only [zero_add,Cloud.shift_zero] at cash
  rw [cash.2]
  simpa only [cofactor,Cloud.shift_zero] using
    priced (K.covariance F tag) (K.symm F tag) 0 (drivers K F tag W A r) (drivers K F tag Y A r)
      (Join.pair s (pick r d)) anchor e E (K.positive F tag).posSemidef
      (by simpa only [zero_add] using submit) _ (Finset.nodup_toList _)

theorem native (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){d r:ℕ}(retained:d≤r)
    (s:R.Mode)(live:s≠R.quiet)(anchor:Precision.Key F G→ℝ):
    let a:=Join.pair s (pick r d)
    let Z:=fun i=>anchored a anchor i (drivers K F tag Y A r i-drivers K F tag W A r i)
    ‖(d.factorial:ℂ)*((observe R r (logMarked (Bulk.Fk K F tag Y A r)) d).part s-
      (observe R r (logMarked (Bulk.Fk K F tag W A r)) d).part s)‖
    ≤expense (K.covariance F tag) (K.symm F tag) 0 (drivers K F tag W A r)
      (drivers K F tag Y A r) a (fun _=>1) (fun i=>stock 1 (Z i)) Finset.univ.toList:=by
  dsimp only
  apply original K F tag W Y A retained s live anchor
  intro i z
  rw [stock_read,map_one,Complex.one_re,one_mul,one_mul]
  nlinarith [sq_nonneg (‖Cloud.paint z (anchored (Join.pair s (pick r d)) anchor i
    (drivers K F tag Y A r i-drivers K F tag W A r i))‖-1/2)]

end YM.Integration.WilsonPositionProgramFiledGaussianPrice
end
