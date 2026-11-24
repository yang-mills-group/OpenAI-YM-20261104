import YM.Integration.WilsonOlderFreshSoftRoseMesh
import YM.Integration.WilsonOriginalPublicFixedCourse

/-! Each of the seven stopped readings follows the actual filed torus preimages of its own sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftRoseNodes
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


open WilsonOriginalPublicFixedCourse (sites digits home)
open WilsonOlderFreshSoftRoseMesh (filed table fare)
open WilsonMaxwellThermometerNominatedSecant (bill)

def anchor (t:Faces):Fin 3:=if h:t.Nonempty then t.min' h else 0

structure TestAt (D:Fin 3→ℕ)(t:Faces) where
  coeff : (i:t)→Knob (D (seat t i))
  phase : t→Chamber
  test : Pen (D ∘ seat t) univ→L[ℝ] ℝ
  bound : ‖test‖≤1

def enrolled (D:Fin 3→ℕ){e:ℕ}(V:Realm G (e+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(N per c:ℕ)(hc:c≤N)(y:Sites N per×Sites N per)(t:Faces)
    (p:TestAt D t):Probe D V t where
  coeff:=p.coeff
  phase:=p.phase
  test:=p.test
  bound:=p.bound
  digit:=draw.symm ▸ fun j i=>digits R per (atOrigin y) j (seat t i)
  root:=fun i=>home R per c hc (atOrigin y) (anchor t) (seat t i)

private theorem retract {α:Type*}(F:α→Type*){a b:α}(h:a=b)(x:F b):
    (h ▸ (show F a from h.symm ▸ x):F b)=x:=by
  cases h
  rfl

/-- The root and its actual next digit are the given original site on the finite physical torus. -/
theorem placed (D:Fin 3→ℕ){e:ℕ}(V:Realm G (e+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(N per c:ℕ)(live:c<N)(y:Sites N per×Sites N per)
    (t:Faces)(p:TestAt D t)(i:t):
    let P:=enrolled R D V draw N per c live.le y t p
    let digits₀:Digits R.family.path.levels t:=draw ▸ P.digit
    wrap (R.family.side (c+1) per) ((R.family.S.oneStep c per).count.val • P.root i+
      lift (digits₀ c i))=(R.family.S.toDepth live per).parent (atOrigin y (seat t i)):=by
  have undo : (draw ▸ (enrolled R D V draw N per c live.le y t p).digit:Digits R.family.path.levels t)=
      fun j i=>digits R per (atOrigin y) j (seat t i):=
    retract (fun L=>Digits L t) draw _
  dsimp only
  rw [undo]
  exact WilsonOriginalPublicFixedCourse.located R per c live (atOrigin y) (anchor t) (seat t i)
def Covered (D:Fin 3→ℕ)(e v start:ℕ)(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(A τ:ℝ):Prop:=
  ∀(A₀:WilsonPositionThermometerCapStation.Group R.family 6)(j:Fin 3→ℕ), (∀a,start≤j a) →
    ∀(N per K c w target:ℕ),v≤w → w≤c → ∀(hc:c≤K)(live:K<N),v+1≤K →
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
    ∀(tests:Sites N per×Sites N per → (t:Faces) → TestAt D t)(q:ℕ),q≤e →
    ∀θ:ℝ,|θ|≤1 → ∀(φ:YM.Test 3)(r:ℝ),
    let probes:=fun y t=>enrolled R D V draw N per c (hc.trans live.le) y t (tests y t)
    let x:=vector R grade j K target η M (filed R A₀) before reg N per
    let Q:=table R D V N per K c w v probes g x pay q θ true
    let F:=table R D V N per K c w v probes g x pay q θ false
    ‖deficit R A₀ φ r F Q‖≤∑y:Sites N per×Sites N per,
      ‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*
        ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (actual R A₀ y) (Q y) t‖*fare R t C ρ logg


theorem purchased {D:Fin 3→ℕ}{e v start:ℕ}{V:Realm G (e+1) Credit.leanC}{A τ:ℝ}
    (draw:V.draws=R.family.path.levels)(sold:WilsonOlderFreshSoftRoseMesh.Activated R D e v start V A τ):
    Covered R D e v start V draw A τ:=by
  intro A₀ j j₀ N per K c w target vw wc kc KN vK warm span η M before reg η0 M0 pay m C D₁ D₂ B ρ
  dsimp only
  intro p0 C0 salary stretch doses clip length tests q keep θ flat φ r
  exact sold A₀ j j₀ N per K c w target vw wc kc KN vK warm span η M before reg η0 M0 pay m C D₁ D₂ B ρ
    p0 C0 salary stretch doses clip length (fun y t=>enrolled R D V draw N per c (kc.trans KN.le) y t (tests y t))
    q keep θ flat φ r

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(e:ℕ)(A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels),
      V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=v ∧ Covered R D e v start V draw A τ:=by
  obtain ⟨start,school⟩:=WilsonOlderFreshSoftRoseMesh.original R paid D fit e A τ a0 τ0
  refine ⟨start,?_⟩
  filter_upwards [school] with v hv
  obtain ⟨V,draw,fees,ys,anchor,issued⟩:=hv
  exact ⟨V,draw,fees,ys,anchor,purchased R draw issued⟩

end YM.Integration.WilsonOlderFreshSoftRoseNodes
end
