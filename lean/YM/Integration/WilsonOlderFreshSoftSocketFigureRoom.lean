import YM.Integration.WilsonOlderFreshSoftRoseIncome

/-! Keep the original occupied input, both soft stops, and its full normalized-scalar tariffs on the same awarded realm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFigureRoom
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

open WilsonOlderFreshSoftRoseNodes (TestAt enrolled Covered)
open WilsonOlderFreshSoftTrialCut (source)
open WilsonOlderFreshSoftMoment (mixed)

open WilsonOlderFreshSoftRoseIncome (Stock)
open private population nonblank from YM.Integration.WilsonOlderFreshSoftRoseIncome

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(e:ℕ)(A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels),
      V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=v ∧
      (∀t:Faces,Dormitory V (mass (grade ∘ seat t) univ) 0 Credit.leanC) ∧
      Covered R D e v start V draw A τ ∧ ∀t:Faces,t.Nonempty → Stock R D e v start V draw A τ t:=by
  let proper:Type:={t:Faces//t.Nonempty}
  have shop:=WilsonOlderFreshSoftRoseMarket.physical paid
  choose cut purchases using fun h:proper=>WilsonOlderFreshSoftTrialCut.original R simple shop grade (seat h.val)
    (D ∘ seat h.val) e univ (nonblank h.property) A τ a0 τ0
  choose gross stocks using fun h:proper=>WilsonOlderFreshSoftTrialSize.original R simple shop grade (seat h.val)
    (D ∘ seat h.val) e univ (nonblank h.property) A τ a0 τ0
  let start:= (∑h:proper,cut h)+(∑h:proper,gross h)
  have early (h:proper):cut h ≤ start:=by
    exact (single_le_sum (f:=cut) (fun _ _=>Nat.zero_le _) (mem_univ h)).trans (Nat.le_add_right ..)
  have earlyG (h:proper):gross h ≤ start:=by
    exact (single_le_sum (f:=gross) (fun _ _=>Nat.zero_le _) (mem_univ h)).trans (Nat.le_add_left ..)
  refine ⟨start,?_⟩
  filter_upwards [eventually_ge_atTop start,WilsonIndependentCollarCensusCourse.original paid 3 grade D fit e 0 0]
    with v onset appointment
  obtain ⟨V,draw,scheme,heat,anchor,_,_,shelf,_⟩:=appointment
  have law:LocalRatio V.paid:=scheme.symm ▸ (RunFormalChain.fromRun R).receipt
  have gradeIncome (t:Faces):Dormitory V (mass (grade ∘ seat t) univ) 0 Credit.leanC:=
    (population grade t).symm ▸ shelf t
  refine ⟨V,draw,scheme,heat,anchor,gradeIncome,?_,?_⟩
  · apply WilsonOlderFreshSoftRoseNodes.purchased R draw
    apply WilsonOlderFreshSoftRoseMesh.admitted R
    intro t ht
    let h:proper:=⟨t,ht⟩
    intro j paidJ N per K c w target vw wc cK KN vK warm window η M Y before reg η0 M0 income m C D₁ D₂ B ρ
    dsimp only
    intro p0 C0 salary stretch doses clip length κ pt cells y f probe q keep tval t1
    have visit:=purchases h v j ((early h).trans onset) (fun a=>(early h).trans (paidJ a))
      (fun a=>(paid.support (j a)).le) V anchor.le draw heat (gradeIncome t) N per K c w target vw wc cK KN vK warm window
      η M Y before reg η0 M0 income m C D₁ D₂ B ρ p0 C0 salary stretch doses clip length κ pt cells y f probe q keep tval t1
    rw [←WilsonOlderFreshSoftCoveredRead.original R (grade ∘ seat t) V.draws V.paid simple law N
      (mass (grade ∘ seat t) univ) w v q vw ((wc.trans cK).trans KN.le) tval]
    exact visit
  · intro t ht A₀ j paidJ N per K c target vc cK KN vK warm window η M before reg η0 M0 pay m C D₁ D₂
    dsimp only
    intro p0 C0 salary stretch doses y test
    let h:proper:=⟨t,ht⟩
    let p:=enrolled R D V draw N per c (cK.trans KN.le) y t test
    have receipt:=stocks h v j ((earlyG h).trans onset) (fun a=>(earlyG h).trans (paidJ a))
      (fun a=>(paid.support (j a)).le) V anchor.le draw heat (gradeIncome t) N per K c target vc cK KN vK warm window
      η M (filed R A₀) before reg η0 M0 pay m C D₁ D₂ p0 C0 salary stretch doses p.coeff p.phase p.digit p.root p.test p.bound
    let x:=fun i:t=>vector R grade j K target η M (filed R A₀) before reg N per (seat t i)
    let P:=source R (D ∘ seat t) (grade ∘ seat t) N K c V.draws V.paid p.coeff p.phase p.digit p.root univ p.test
    let g:=regulatorRun R.family N per K
    have positive:0≤WilsonOlderFreshSoftTrialCharge.bill R grade (seat t) C:=by
      apply prod_nonneg
      intro i _
      exact mul_nonneg (by unfold WilsonOlderFreshSoftTrialSalary.base WilsonOlderFreshSoftTrialSalary.wrap;positivity) (C0 _)
    exact ⟨fun q keep r=>(WilsonOlderFreshSoftMoment.original R (grade ∘ seat t) g x P q r (receipt q keep r).1).2.1,
      WilsonOlderFreshSoftMoment.ranks R (grade ∘ seat t) g x P (mass (grade ∘ seat t) univ) e _ _
        (prod_nonneg fun i _=>p0 _) (mul_nonneg positive (Real.exp_pos _).le) receipt⟩

end YM.Integration.WilsonOlderFreshSoftSocketFigureRoom
end
