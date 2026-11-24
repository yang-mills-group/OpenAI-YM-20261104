import YM.Integration.WilsonReceivedCompactQUnitLedger
import YM.Integration.ActualScalarTransport

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedQUnitPosterior
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
open MergeProof.Accent RG3.Law OPE.Therm Extra.Trajectories Extra.Histories Trace.Physical.GermGraph
variable {G:Gauge} (R:Run G) {N per:ℕ}
local notation "C₀" => R.family
local notation "H₀" => R.family.path

private theorem join {b i t:ℕ} (bi:b ≤ i) (it:i ≤ t) (f:Config G (R.family.side t per) → ℂ) :
    gust (H₀) N per i (gust (H₀) N per t f i it) b bi=gust (H₀) N per t f b (bi.trans it) := by
  induction bi using Nat.decreasingInduction with
  | self=>rw [gust_base]
  | of_succ l hl ih=>rw [gust_step (H₀) N per i _ hl,gust_step (H₀) N per t _ (hl.trans_le it),ih]

theorem raw (b n:ℕ) (f:Config G (R.family.side (b+n) per) → ℂ) :
    flow (C₀) 0 N per b n f=gust (H₀) N per (b+n) f b (Nat.le_add_right b n) := by
  induction n with
  | zero=>exact (gust_base (H₀) N per b f).symm
  | succ n ih=>
    change flow (C₀) 0 N per b n (GermGraph.transition (C:=C₀) 0 N per (b+n) f)=_
    have single:GermGraph.transition (C:=C₀) 0 N per (b+n) f=
        gust (H₀) N per (b+n+1) f (b+n) (Nat.le_succ (b+n)) := by
      rw [gust_step (H₀) N per (b+n+1) f (Nat.lt_succ_self (b+n)),gust_base]
      simp only [GermGraph.transition,blast,pow_zero,one_smul]
    rw [ih,single]
    exact join R (Nat.le_add_right b n) (Nat.le_succ (b+n)) f

variable {m k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable (b n:ℕ)
local notation "edge" => Nat.le_add_right b n
local notation "trueW" i:max => (R.family.path.rep N per i)
local notation "μ" i:max => scene (H₀) N per i

include course in
theorem normalized (floor:m ≤ b) (live:b+n ≤ N) (f:Config G (R.family.side (b+n) per) → ℂ) :
    actualTransport (C₀) (N:=N) (fun U=>((Ψ (b+n)).eval U)⁻¹ • f U) (edge)=
      fun V=>((Ψ b).eval V)⁻¹ • flow (C₀) 0 N per b n f V := by
  have top:(Ψ (b+n)).eval=(trueW (b+n)).eval:=(course.1.walk (b+n) (by omega) live).view
  have bottom:(Ψ b).eval=(trueW b).eval:=(course.1.walk b floor (by omega)).view
  have cancel:(fun U=>(trueW (b+n)).eval U • (((trueW (b+n)).eval U)⁻¹ • f U))=f := by
    funext U
    have nv:(trueW (b+n)).eval U≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    rw [smul_smul,mul_inv_cancel₀ nv,one_smul]
  unfold actualTransport
  rw [top,bottom,cancel,raw]

def Viewed (source:Config G (R.family.side (b+n) per) → ℂ) (residual:Config G (R.family.side b per) → ℂ) (z:ℂ) :Prop :=
  let full:=fun U=>((Ψ (b+n)).eval U)⁻¹ • source U
  let rest:=fun V=>((Ψ b).eval V)⁻¹ • residual V
  (∀j (earlier:j ≤ b),actualTransport (C₀) (N:=N) full (earlier.trans (edge))=
     actualTransport (C₀) (N:=N) (fun V=>rest V+z) earlier) ∧
  (Integrable rest (μ b)) ∧
    ∀j (earlier:j ≤ b),(∫V,actualTransport (C₀) (N:=N) full (earlier.trans (edge)) V ∂(μ j))=(∫U,rest U ∂(μ b))+z

include course in
theorem original (floor:m ≤ b) (live:b+n ≤ N)
    (source:Config G (R.family.side (b+n) per) → ℂ) (residual:Config G (R.family.side b per) → ℂ) (z:ℂ)
    (report:flow (C₀) 0 N per b n source=fun V=>residual V+z*((Ψ b).eval V:ℂ))
    (paid:Integrable residual (prior G _)) : Viewed (N:=N) R Ψ b n source residual z := by
  let rest:=fun V=>((Ψ b).eval V)⁻¹ • residual V
  have hb:b ≤ N:=by omega
  have bottom:(Ψ b).eval=(trueW b).eval:=(course.1.walk b floor hb).view
  have positive V:0<(Ψ b).eval V:=by rw [bottom];exact Multi.AxisShift.chosen_positive R.makes.wilson hb V
  have cancel V:(trueW b).eval V • rest V=residual V := by
    dsimp only [rest]
    have nv:(trueW b).eval V≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson hb V).ne'
    rw [bottom,smul_smul,mul_inv_cancel₀ nv,one_smul]
  have wi:Integrable (fun V=>(trueW b).eval V • rest V) (prior G _):=(funext cancel).symm ▸ paid
  have stop:actualTransport (C₀) (N:=N) (fun U=>((Ψ (b+n)).eval U)⁻¹ • source U) (edge)=fun V=>rest V+z := by
    rw [normalized R π Γ Ψ course b n floor live,report]
    funext V
    have nz:((Ψ b).eval V:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (positive V).ne'
    dsimp only [rest]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    field_simp
  have tower j (age:j ≤ b) :=(actualTransport_tower (C₀) R.makes live (fun U=>((Ψ (b+n)).eval U)⁻¹ • source U) (edge) age).symm
  have same j (age:j ≤ b):actualTransport (C₀) (N:=N) (fun U=>((Ψ (b+n)).eval U)⁻¹ • source U) (age.trans (edge))=
      actualTransport (C₀) (N:=N) (fun V=>rest V+z) age := by rw [←stop];exact tower j age
  have ib:=actualScene_integrable_of_weighted (C₀) R.makes hb wi
  have vb:=vac_integrable (H₀) N per b R.makes.wilson hb
  have cz:Integrable (fun V=>(trueW b).eval V • z) (prior G _) := by
    simpa only [Complex.real_smul,liftVac] using vb.mul_const z
  have summed:Integrable (fun V=>(trueW b).eval V • (rest V+z)) (prior G _) := by
    simp only [smul_add]
    exact wi.add cz
  refine ⟨same,ib,?_⟩
  intro j age
  letI:IsProbabilityMeasure (μ b):=OPE.Therm.probability R.makes.wilson hb
  rw [same j age,actualScene_transport (C₀) R.makes hb summed age,integral_add ib (integrable_const z),integral_const]
  simp [rest,Complex.real_smul,Complex.ofReal_inv]

end YM.Integration.WilsonReceivedQUnitPosterior
