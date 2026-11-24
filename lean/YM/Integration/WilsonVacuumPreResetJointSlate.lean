import YM.Integration.WilsonVacuumPreResetJointLanded
import YM.Integration.WilsonVacuumPreResetJointBanks

/-! The entire unmasked old spring, with its measured kinetic and coupling
coefficients, and its independently filed winding polynomial on the same
finite torus. All three inherited signed interactions are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointSlate
open WilsonCoeffUV
open Filter Function Finset Lattice Wilson RG Laurent Bloch Exterior Blue FreeResolvent Precision
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Stationary Work.G05 Tree Pressure Pressure.Stores Pressure.Tube
open Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 SliceRows Coat Matter Blaze RG01.Sounder
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointBanks
open WilsonLimitConstruction OriginalMarkedRunAction Analysis
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def physical (B : Clip) (K : PathData G) (A : SeriesA G) (γ η ρ u : ℝ) (U : Config G f) : ℝ :=
  γ*secondTerm B K U + η*interaction K U + ρ*FundedPeriodAction.rendered f A u U

def published (B : Clip) (K : PathData G) (A : SeriesA G) (γ η ρ u : ℝ) (d : ℕ)
    (Z : Coat T F) (w : Arguments G c f) : ℝ :=
  γ*B.direct*(∑ x : Site f, WilsonVacuumPreResetJointFace.paper univ Z d x w) +
  γ*WilsonVacuumPreResetJointLanded.numerical (kinetic K) d Z w +
  η*(WilsonVacuumPreResetJointLanded.numerical (cubic K) d Z w +
    WilsonVacuumPreResetJointLanded.numerical (quartic K) d Z w) +
  ρ*WilsonVacuumPreResetJointLanded.filed A u d Z w

def tariff (B : Clip) (A : SeriesA G) (s C σ D γ η ρ u : ℝ) (j r : ℕ) (t : ℝ) : ℝ :=
  (Fintype.card PlaqAxes:ℝ) * (|γ*B.direct| *WilsonVacuumPreResetJointFace.charge G j r t) +
  |γ| *WilsonVacuumPreResetJointStack.rowBill G s (gramCost G C) 2 j r t +
  |η| *WilsonVacuumPreResetJointStack.rowBill G s C 3 j r t +
  |η| *WilsonVacuumPreResetJointStack.rowBill G s C 4 j r t +
  WilsonVacuumPreResetJointStack.charge A σ D ρ u j r t

theorem original {B : Clip} {K : PathData G} {s C Λ σ D : ℝ}
    (paid : K.Bounds B s C Λ) (hs : 0<σ) (A : SeriesA G) (draw : Draw A σ D)
    (X : Coat T F) (p : Molecule S) (kept : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (γ η ρ u : ℝ) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} {t : ℝ} (ht : 0<t) (ht' : t≤1) (read : Brush j t 1 z y) :
    let Z := (Matter.planted X p).wrapY Y
    Brush j ((Fintype.card (Site f):ℝ)*tariff B A s C σ D γ η ρ u j r t) 1
      (fun w => physical B K A γ η ρ u (field univ Z (z w)) - published B K A γ η ρ u (r+2) Z (z w)) y := by
  intro Z
  obtain ⟨bank0,bank3,bank4⟩ := commission paid
  have face := Brush.spree (univ : Finset (Site f)) _
    (fun _ => (Fintype.card PlaqAxes:ℝ)*(|γ*B.direct| *WilsonVacuumPreResetJointFace.charge G j r t)) zero_le_one
    (fun x _ => WilsonVacuumPreResetJointFace.measured univ Z x r j (γ*B.direct) ht ht' read)
  simp only [sum_const,card_univ,nsmul_eq_mul] at face
  have second := WilsonVacuumPreResetJointLanded.measured (kinetic K) paid.width bank0 X p kept sun Y γ r j ht ht' read
  have third := WilsonVacuumPreResetJointLanded.measured (cubic K) paid.width bank3 X p kept sun Y η r j ht ht' read
  have fourth := WilsonVacuumPreResetJointLanded.measured (quartic K) paid.width bank4 X p kept sun Y η r j ht ht' read
  have remaining := WilsonVacuumPreResetJointLanded.original A hs draw X p kept sun Y ρ u r j ht ht' read
  have all := (((face.gathering second).gathering third).gathering fourth).gathering remaining
  unfold tariff
  simp only [mul_add]
  apply all.shimmy (Filter.Eventually.of_forall fun w => ?_)
  unfold physical published
  rw [rawKinetic paid,rawInteraction B]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum,Z]
  ring

end YM.Integration.WilsonVacuumPreResetJointSlate
