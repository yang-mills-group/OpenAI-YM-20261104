import YM.Integration.WilsonUniformUnmarkedFiniteStrip
import YM.Integration.WilsonRunKineticPeriodIncome

/-! Every positive order of the true reset finite Wilson course has zero
rooted kinetic position moment, on every selected physical period and at
every cutoff, including the Wilson top. No torus limit is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedAffineMoment
open Filter Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorBulkHistory
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple bought in
theorem calibrated (N per j e : ℕ) (live : j ≤ N) :
    caliper (R.family.side j per) (Lis.sun G u) (coeff e (placed R u wood tags N per j))=0 := by
  obtain ⟨S,law,data⟩:=WilsonUniformUnmarkedCourse.actual R simple u V bought wood tags N per j e live
  have fields:=(data j le_rfl live).1
  have zero : caliper (R.family.side j per) (Lis.sun G u) (coeff e (S.Poly j))=0 := by
    rcases live.lt_or_eq with lt | eq
    · exact (WilsonConditionalTaylorSceneCalibration.received R law j le_rfl lt).2.2.2 e le_rfl
    · subst j
      rw [law.opening]
      exact MSbar.Midpoint.born _ _ _
  rw [←WilsonConditionalTaylorKineticProjection.two (Lis.sun G u) _,←fields e le_rfl 2 (by norm_num),
    WilsonConditionalTaylorKineticProjection.two]
  exact zero

include simple bought in
theorem rooted (N per j e : ℕ) (live : j ≤ N) (positive : 0<e) :
    let n:=R.family.side j per
    let A:=course R u wood tags N j n
    (∑ x : Site n, rancho A e 2 ![(x,coord (1:Axis),u),(0,coord (1:Axis),u)] *
      (Cork.ch 0 (lift x)*Cork.ch 0 (lift x)))=0 := by
  intro n A
  let v:=Lis.sun G u
  let F:=place (WilsonMovingGaussianCoordinates.link G n).symm A
  have z:=calibrated R simple u V bought wood tags N per j e live
  change caliper n v (coeff e (splitV F))=0 at z
  rw [WilsonConditionalTaylorFieldReset.positive F positive] at z
  have civic : Civic A :=(admitted R u wood tags N j live n).2.2
  have norm:=WilsonRunKineticPeriodIncome.measured A e u civic
  have debt:=norm.symm.trans z
  linarith only [debt]

end YM.Integration.WilsonUniformUnmarkedAffineMoment
