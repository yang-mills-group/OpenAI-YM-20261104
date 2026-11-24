import YM.Integration.WilsonPhysicalHistoryRetainedSpringPolynomial
import YM.Integration.WilsonPhysicalHistoryRetainedSpringAllFiled

/-! The full old rooted polynomial reads the same site action issued on this
run, with its actual period, older vacuum and finite kinetic reset. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open LocalComparison Marker Global FullQLocal IterationFour IterationFour.Vacuum
open Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat Push Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Malachite
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoherentMayerHearing WilsonPositionSeparatedProfileMayerWickInputs
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem scaled_degree {E : Type*} [DecidableEq E] (r : ℝ) (A : Normal.poly E) {d : ℕ} (bound : A.totalDegree≤d) :
    (MvPolynomial.C (r:ℂ)*A).totalDegree≤d:=by
  exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact bound)

private theorem add_degree {E : Type*} [DecidableEq E] (A B : Normal.poly E) {n : ℕ}
    (a : A.totalDegree≤n) (b : B.totalDegree≤n) : (A+B).totalDegree≤n:=
  (MvPolynomial.totalDegree_add ..).trans (max_le a b)

theorem spring_polynomial_degree {u f : Side} {S : StepData u f} {T : Tube G S} {F : Forest S.ratio}
    (X : Coat T F) (B : Clip) (path : PathData G) (Z : SeriesA G)
    {σ D Λ τ C : ℝ} (previous : path.Bounds B σ D Λ) (ht : 0<τ) (filed : Draw Z τ C)
    (d : ℕ) (grade : ∀a∈Z,a.grade≤d) (γ w b c : ℝ) (x : Site f) (K : ℕ) (g : ℝ) :
    (springPolynomial X B path Z γ w b c x K g).totalDegree≤ max (d+1) 3+K := by
  have faces:=(face_portfolio X x K g).1
  have gram:=(site_portfolio X (gramEntries path) (by decide) previous.width (gram_finance path previous) x K g).1
  have tri:=(site_portfolio X path.cubic (by decide) previous.width previous.three x K g).1
  have four:=(site_portfolio X path.quartic (by decide) previous.width previous.four x K g).1
  unfold springPolynomial
  apply add_degree
  · apply add_degree
    · exact scaled_degree _ _ (add_degree _ _ (scaled_degree _ _ (faces.trans (by omega))) (gram.trans (by omega)))
    · exact scaled_degree _ _ (add_degree _ _ (tri.trans (by omega)) (four.trans (by omega)))
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    have mem:=List.get_mem Z i
    have high:=((Z.get i).rankA).trans (grade _ mem)
    exact scaled_degree _ _ ((site_portfolio X (Z.get i).cells (by omega) ht (filed.2 _ mem).toll x K g).1.trans (by omega))

def registeredSpring (R : Run G) (N per j r : ℕ) (Z : SeriesA G)
    {u : Side} {S : StepData u (R.family.side j per)} {T : Tube G S} {F : Forest S.ratio}
    (X : Coat T F) (x : Site (R.family.side j per)) (K : ℕ) (g : ℝ) : Normal.poly (Eye X) :=
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  springPolynomial X (R.family.path.levels.params j).clip (R.family.path.rep N per j).path Z
    γ (γ+R.alloy.B.kin.alpha N j) (Integral.temperature g*p) (g/Real.sqrt p) x K g

theorem registered_spring (R : Run G) (N per j r : ℕ) (later : j≤N) (Z : SeriesA G)
    {τ C : ℝ} (ht : 0<τ) (filed : Draw Z τ C) (d : ℕ) (grade : ∀a∈Z,a.grade≤d)
    {u : Side} {S : StepData u (R.family.side j per)} {T : Tube G S} {F : Forest S.ratio}
    (X : Coat T F) (x : Site (R.family.side j per)) (K : ℕ) (g : ℝ) :
    let V:=R.family.path.levels
    let D:=V.params j
    let p:=finitePitch R N j r g
    let γ:=g^2*pitchTail R N j r g
    let P:=registeredSpring R N per j r Z X x K g
    P.totalDegree≤ max (d+1) 3+K ∧
    Rise.coin P≤ springPolynomialPrice G D.clip Z D.width D.paths τ C γ (γ+R.alloy.B.kin.alpha N j)
      (Integral.temperature g*p) (g/Real.sqrt p) K g ∧
    ∀ z : Air (R.family.side j per) G,Cloud.paint (fun u=>z (tube X u)) P=
      springTaylorAt R N per j r Z x (angularSample F z) K g := by
  intro V D p γ P
  have rep : R.family.path.Conv N per j:=R.makes.wilson.represents N per j later
  have previous : (R.family.path.rep N per j).path.Bounds D.clip D.width D.paths (V.clock.loopCap j):=by
    dsimp only [D,V];rw [←rep.clip];exact rep.good.paths
  exact ⟨spring_polynomial_degree X _ _ Z previous ht filed d grade ..,
    spring_polynomial_price X _ _ Z previous ht filed ..,fun z=>spring_polynomial_read X _ _ Z previous ht filed _ _ _ _ x K g z⟩

end YM.Integration.OriginalMarkedRunAction
