import YM.Integration.WilsonOriginalObservedRoseBornHeat

/-! The absolute signal at the issued physical cutoffs after the acquired quadratic expense has been removed. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornSignal
open Filter Metric Finset PowerSeries Set Lattice Wilson Maxwell XSpace XSpace.Rose XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.WilsonBridge.Coupling
open RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Normalize
open WilsonOriginalObservedRoseBornLedger (truncation)
open WilsonOriginalObservedRoseBornMeasured (mismatch)
open WilsonOriginalObservedRoseBornPosition (Balance)
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerOriginal (lower)
open Pert.Asymptotics OPE OPE.Orbits Trace Next.UVStress RG17 PhysMS.Frame Precision XSpace.Photo
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open WilsonOriginalObservedRoseBornRatio (Visit tariff)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}(simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G){fine index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {I:Type}[Fintype I](basis:Module.Basis I ℂ (Sec G 6))(cap:ℝ→ℝ)
    (fronts:ℝ→Set Mesh)(admitted:∀r,fronts r∈Front)
    {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}(bliss:Bliss F l z H)
local notation "cut" => trail.curry (l:Filter (ℕ×ℕ))
local notation "g" => regulatorRun R.family
local notation "gas" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine

def unpaid (Z:WilsonPrescription G){Y:Type}[Fintype Y](μ:Y→ℂ)(points:Y→Sample 3)(rows:Y→Badge→ℂ)
    (m:Mesh)(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4))(t:ℝ):ℝ:=
  truncation Z.scheme (V:=Z.store) μ points (tag G) 1 (t:ℂ)+|mismatch Z μ 1 points rows m u P Q t|

include hB pace schedule admitted bliss in
theorem original :
    ∃m:ℝ→Mesh,(∀r,m r∈fronts r) ∧ ∀(Y:Visit→Type)[∀w,Fintype (Y w)]
      (μ:∀w,Y w→ℂ)(points:∀w,Y w→Sample 3)(rows:∀w,Y w→Badge→ℂ)
      (u:Visit→Sec G 6)(P Q:Visit→Module.End ℂ (Sec G 4))(top:Visit→ℂ)(earned:Visit→ℝ)(A:ℝ),
      (∀ᶠw in cut, Equivariant (P w) ∧ Equivariant (Q w) ∧
        cost basis (roster (u w) (P w (lower G)) (Q w (lower G)))≤cap w.1 ∧
        Balance Z (μ w) 1 (points w) (g w.2.1 w.2.2) w.2.1 (rows w) (top w) (earned w) ∧
        0≤earned w ∧ earned w≤A*(wilson z w.1)^2) →
      Tendsto (fun w=>unpaid Z (μ w) (points w) (rows w) (m w.1) (u w) (P w) (Q w) (gas w)/gas w)
        cut (𝓝 0) →
      Tendsto (fun w=>(top w).re/gas w) cut (𝓝 (c_T Z.criterion:ℝ)) ∧
      Tendsto (fun w=>((top w).re/(c_T Z.criterion:ℝ))/gas w) cut (𝓝 1):=by
  obtain ⟨m,offered,read⟩:=WilsonOriginalObservedRoseBornRatio.original R simple hB pace Z schedule
    basis cap fronts admitted bliss.lies
  refine ⟨m,offered,?_⟩
  have heat:=WilsonOriginalObservedRoseBornHeat.original R simple hB pace Z schedule bliss.lies
    (wilson_link F simple bliss.budgets bliss.keen bliss.lies)
  intro Y inst μ points rows u P Q top earned A paid restored
  have funds:Tendsto (fun w=>earned w/gas w) cut (𝓝 0):=by
    have bound:Tendsto (fun w:Visit=>A*((wilson z w.1)^2/gas w)) cut (𝓝 0):=by
      simpa only [mul_zero] using (tendsto_const_nhds (x:=A)).mul heat.2.2
    apply squeeze_zero' _ _ bound
    · filter_upwards [paid,heat.1] with w account live using div_nonneg account.2.2.2.2.1 live.1.le
    · filter_upwards [paid,heat.1] with w account live
      rw [←mul_div_assoc]
      exact div_le_div_of_nonneg_right account.2.2.2.2.2 live.1.le
  have reading:=read Y μ points rows u P Q top earned
  have count:Tendsto (fun w=>(top w).re/gas w) cut (𝓝 (c_T Z.criterion:ℝ)):=by
    apply reading
    · filter_upwards [paid,heat.1] with w account live using
        ⟨account.1,account.2.1,account.2.2.1,live.2,account.2.2.2.1⟩
    · have all:=funds.add restored
      rw [zero_add] at all
      apply all.congr
      intro w
      unfold unpaid WilsonOriginalObservedRoseBornRatio.tariff WilsonMaxwellThermometerKineticFineRose.axis
      ring
  refine ⟨count,?_⟩
  have nz:(c_T Z.criterion:ℝ)≠0:=Z.criterion.fresh.ne
  have scale:=count.div_const (c_T Z.criterion:ℝ)
  rw [div_self nz] at scale
  apply scale.congr
  intro w
  ring

end YM.Integration.WilsonOriginalObservedRoseBornSignal
