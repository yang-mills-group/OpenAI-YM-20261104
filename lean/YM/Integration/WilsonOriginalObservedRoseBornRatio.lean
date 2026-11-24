import YM.Integration.WilsonOriginalObservedRoseBornMeter
import YM.Integration.WilsonOriginalObservedRoseThermal

/-! The remaining first-order bill consists of signed seven-face and finite-ground transfers on the original ordered regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornRatio
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
open scoped Classical Topology
abbrev Visit:=ℝ×(ℕ×ℕ)
variable {G:Gauge}(R:Run G)(simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G){fine index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {I:Type}[Fintype I](basis:Module.Basis I ℂ (Sec G 6))(cap:ℝ→ℝ)
    (fronts:ℝ→Set Mesh)(admitted:∀r,fronts r∈Front)
    {f:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}(prior:(l:Filter _)≤f.fuse)
local notation "cut" => trail.curry (l:Filter (ℕ×ℕ))
local notation "g" => regulatorRun R.family
local notation "gas" => fun w:Visit=>g w.2.1 w.2.2 (fine w.1)

def tariff (Z:WilsonPrescription G){Y:Type}[Fintype Y](μ:Y→ℂ)(points:Y→Sample 3)(rows:Y→Badge→ℂ)
    (m:Mesh)(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4))(t earned:ℝ):ℝ:=
  earned+truncation Z.scheme (V:=Z.store) μ points (tag G) 1 (t:ℂ)+|mismatch Z μ 1 points rows m u P Q t|

include admitted hB pace schedule prior in
theorem original :
    ∃m:ℝ→Mesh,(∀r,m r∈fronts r) ∧ ∀(Y:Visit→Type)[∀w,Fintype (Y w)]
      (μ:∀w,Y w→ℂ)(points:∀w,Y w→Sample 3)(rows:∀w,Y w→Badge→ℂ)
      (u:Visit→Sec G 6)(P Q:Visit→Module.End ℂ (Sec G 4))(top:Visit→ℂ)(earned:Visit→ℝ),
      (∀ᶠw in cut, Equivariant (P w) ∧ Equivariant (Q w) ∧
        cost basis (roster (u w) (P w (lower G)) (Q w (lower G)))≤cap w.1 ∧
        ‖((gas w):ℂ)‖≤1 ∧ Balance Z (μ w) 1 (points w) (g w.2.1 w.2.2) w.2.1 (rows w) (top w) (earned w)) →
      Tendsto (fun w=>tariff Z (μ w) (points w) (rows w) (m w.1) (u w) (P w) (Q w) (gas w) (earned w)/gas w)
        cut (𝓝 0) →
      Tendsto (fun w=>(top w).re/gas w) cut (𝓝 (c_T Z.criterion:ℝ)):=by
  obtain ⟨m,offered,_,ground⟩:=WilsonOriginalObservedRoseBornGround.original R simple hB pace Z
    schedule basis cap fronts admitted
  refine ⟨m,offered,?_⟩
  intro Y inst μ points rows u P Q top earned book bought
  apply Metric.tendsto_nhds.mpr
  intro ε εp
  have event:∀ᶠw:Visit in cut,fine w.1≤w.2.1 ∧
      ‖coeff 1 (Detector Z.scheme Z.criterion (m w.1))-((c_T Z.criterion:ℝ):ℂ)‖≤w.1 ∧
      ∀(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4)),Equivariant P→Equivariant Q→
        cost basis (roster u (P (lower G)) (Q (lower G)))≤cap w.1→
        ‖credit Z.scheme Z.criterion (m w.1) u (P (lower G)) (Q (lower G))/(gas w:ℂ)‖≤2*w.1:=by
    apply eventually_curry_iff.mpr
    filter_upwards [ground] with r paid
    filter_upwards [(large_mesh f (fine r)).filter_mono prior] with z available
    exact ⟨available,paid.1,paid.2 z.1 z.2 available⟩
  have width:∀ᶠw:Visit in cut,w.1<ε/6:=by
    apply eventually_curry_iff.mpr
    have small:∀ᶠr:ℝ in trail,r<ε/6:=(eventually_lt_nhds (by positivity : (0:ℝ)<ε/6)).filter_mono nhdsWithin_le_nhds
    exact small.mono fun _ hr=>Eventually.of_forall fun _=>hr
  filter_upwards [event,book,width,(tendsto_order.1 bought).2 (ε/2) (by positivity)] with w e b narrow cash
  let t:=gas w
  let a:ℝ:=c_T Z.criterion
  let bill:=tariff Z (μ w) (points w) (rows w) (m w.1) (u w) (P w) (Q w) t (earned w)
  let d:=mismatch Z (μ w) 1 (points w) (rows w) (m w.1) (u w) (P w) (Q w) t
  have hot:0<t:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson e.1))
  have h:=WilsonOriginalObservedRoseBornMeter.original Z (μ w) 1 (points w) (rows w) (m w.1)
    (u w) (P w) (Q w) w.1 (g w.2.1 w.2.2) w.2.1 (fine w.1) e.1 (top w) (earned w) b.2.2.2.2 hot
    b.2.2.2.1 (e.2.2 _ _ _ b.1 b.2.1 b.2.2.1) e.2.1
  have total:|(top w).re-a*t|≤bill+3*w.1*t:=by
    calc
      _=|(top w).re-a*t-d+d|:=by ring_nf
      _≤|(top w).re-a*t-d|+|d|:=abs_add_le .. 
      _≤_:=by dsimp only [bill,tariff,d,a,t];linarith
  change dist ((top w).re/t) a<ε
  rw [Real.dist_eq,div_sub' hot.ne',mul_comm t a,abs_div,abs_of_pos hot]
  apply (div_le_div_of_nonneg_right total hot.le).trans_lt
  have split:(bill+3*w.1*t)/t=bill/t+3*w.1:=by field_simp
  rw [split]
  change bill/t<ε/2 at cash
  linarith

end YM.Integration.WilsonOriginalObservedRoseBornRatio
