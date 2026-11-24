import YM.Integration.WilsonOlderFreshSoftRoseMarket
import YM.Integration.WilsonOlderFreshSoftRoseSecant

/-! The actual named cutoff vectors and the seven proper shifted readings share one moving-stop bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftRoseMesh
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor
open WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {crop:Campaign R} {W:Campaign.Pillars R crop}

open WilsonOlderFreshSoftRoseCourse (grade seat Hearing)
open WilsonOlderFreshSoftTrialCharge (power bill)


open WilsonOlderFreshSoftRoseMarket (Probe row scaled)
open WilsonOlderFreshSoftRoseSecant (deficit actual)
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (atOrigin)

variable (R) (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "Faces" => Finset (Fin 3)
local notation "Sites" N:max per:max => Site (R.family.side N per)

def filed (i:Fin 3)(z:ℕ×ℕ):R.family.label (grade i):=named R A₀ z.1 z.2 i

def table {e:ℕ}(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)(N per K c w v:ℕ)
    (probes:Sites N per×Sites N per → (t:Faces) → Probe D V t)
    (g:ℝ)(x:∀i,(R.family.labels.level (grade i)).Coeff)(pay:Fin 3→ℝ)(q:ℕ)(θ:ℝ)(early:Bool)
    (y:Sites N per×Sites N per)(t:Faces):ℂ:=
  if t.Nonempty then scaled t pay (row (R:=R) D V t N K c w v (probes y t) g x q θ early) else 1

def fare (t:Faces)(C:Fin 3→ℝ)(ρ logg:ℝ):ℝ:=
  if t.Nonempty then bill R grade (seat t) C*Real.exp (-ρ*logg) else 0

def Activated (D:Fin 3→ℕ)(e v start:ℕ)(V:Realm G (e+1) Credit.leanC)(A τ:ℝ):Prop:=
  ∀(A₀:WilsonPositionThermometerCapStation.Group R.family 6)(j:Fin 3→ℕ), (∀a,start≤j a) →
    ∀(N per K c w target:ℕ),v≤w → w≤c → c≤K → K<N → v+1≤K →
    2≤R.family.path.levels.clock.hatBeta K →
    R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1))) →
    ∀(η:ℝ)(M:Fin 3→ℝ)(before:∀a,j a≤K)
      (reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R grade j target η M (filed R A₀)),
      0≤η → (∀a,0≤M a) → ∀(pay m C D₁ D₂:Fin 3→ℝ)(B ρ:ℝ),
    let g:=regulatorRun R.family N per K
    let logg:=Real.log g⁻¹
    (∀a,0≤pay a) → (∀a,0≤C a) → (∀a,M a≤C a*Real.exp ((2*m a)*logg)) →
    (∀a,Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹≤D₁ a*logg) →
    (∀a,pay a≤Real.exp ((grade a:ℝ)*D₂ a*logg)) →
    R.family.S.a c/R.family.S.a w≤Real.exp (-B*logg) →
    (∀t:Faces,t.Nonempty → power R grade (seat t) m η D₁ D₂+τ+ρ≤B/4) →
    ∀(probes:Sites N per×Sites N per → (t:Faces) → Probe D V t)(q:ℕ),q≤e →
    ∀θ:ℝ,|θ|≤1 → ∀(φ:YM.Test 3)(r:ℝ),
    let x:=vector R grade j K target η M (filed R A₀) before reg N per
    let Q:=table R D V N per K c w v probes g x pay q θ true
    let F:=table R D V N per K c w v probes g x pay q θ false
    ‖deficit R A₀ φ r F Q‖≤∑y:Sites N per×Sites N per,
      ‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*
        ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (actual R A₀ y) (Q y) t‖*fare R t C ρ logg

theorem admitted {D:Fin 3→ℕ}{e v start:ℕ}{V:Realm G (e+1) Credit.leanC}{A τ:ℝ}
    (faces:∀t:Faces,t.Nonempty → Hearing R grade D e v start V t A τ):Activated R D e v start V A τ:=by
  intro A₀ j paidJ N per K c w target vw wc cK KN vK warm window η M before reg η0 M0 pay m C D₁ D₂ B ρ
  dsimp only
  intro p0 C0 salary stretch doses clip length probes q keep θ flat φ r
  apply WilsonOlderFreshSoftRoseSecant.priced
  intro y t
  by_cases ht:t.Nonempty
  · simp only [table,fare,if_pos ht]
    exact WilsonOlderFreshSoftRoseMarket.issued (faces t ht) j paidJ N per K c w target vw wc cK KN vK warm window η M (filed R A₀) before reg η0 M0 pay m C D₁ D₂ B ρ p0 C0 salary stretch doses clip (length t ht) (probes y t) q keep θ flat
  · simp [table,fare,ht]

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(e:ℕ)(A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀ᶠ v:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=v ∧
      Activated R D e v start V A τ:=by
  obtain ⟨start,book⟩:=WilsonOlderFreshSoftRoseMarket.original paid D fit e A τ a0 τ0
  refine ⟨start,?_⟩
  filter_upwards [book] with v hv
  obtain ⟨V,calendar,costs,soft,anchor,faces⟩:=hv
  exact ⟨V,calendar,costs,soft,anchor,admitted R faces⟩

end YM.Integration.WilsonOlderFreshSoftRoseMesh
end
