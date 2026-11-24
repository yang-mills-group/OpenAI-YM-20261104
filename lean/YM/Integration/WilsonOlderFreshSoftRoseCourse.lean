import YM.Integration.WilsonOlderFreshSoftTrialCourse
import YM.Integration.WilsonPositionThermometerGradedSource

/-! All seven ordinary children share one original court, measured quiet and finite period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftRoseCourse
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

def grade (i:Fin 3):ℕ:=WilsonPositionThermometerGradedSource.grade i
def seat (t:Finset (Fin 3))(i:t):Fin 3:=i.val

private theorem population (d:Fin 3→ℕ)(t:Finset (Fin 3)):
    mass (d ∘ seat t) (univ:Finset t)=mass d t:=by
  change (∑i:t,d i)=∑i∈t,d i
  exact Finset.sum_coe_sort t d

private theorem nonblank {t:Finset (Fin 3)}(h:t.Nonempty):(univ:Finset t).Nonempty:=by
  obtain ⟨i,hi⟩:=h
  exact ⟨⟨i,hi⟩,mem_univ _⟩

def Hearing (R:Run G)(d D:Fin 3→ℕ)(e v start:ℕ)(S:Realm G (e+1) Credit.leanC)
    (t:Finset (Fin 3))(A τ:ℝ):Prop:=
    ∀(j:Fin 3→ℕ),(∀a,start≤j a) → ∀(N per K c w target:ℕ),v≤w → w≤c → c≤K → K<N → v+1≤K →
    2≤R.family.path.levels.clock.hatBeta K →
    R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1))) →
    ∀(η:ℝ)(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
      (before:∀a,j a≤K)(reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y),
      0≤η → (∀a,0≤M a) → ∀(paid m C D₁ D₂:Fin 3→ℝ)(B ρ:ℝ),
    let g:=regulatorRun R.family N per K
    let s:=Real.log g⁻¹
    (∀a,0≤paid a) → (∀a,0≤C a) → (∀a,M a≤C a*Real.exp ((2*m a)*s)) →
    (∀a,Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹≤D₁ a*s) →
    (∀a,paid a≤Real.exp ((d a:ℝ)*D₂ a*s)) →
    R.family.S.a c/R.family.S.a w≤Real.exp (-B*s) → power R d (seat t) m η D₁ D₂+τ+ρ≤B/4 →
    ∀(κ:(i:t)→Knob (D (seat t i)))(pt:t→Chamber)(cells:Digits S.draws t)(y:t → Cover)(f:Pen (D ∘ seat t) univ→L[ℝ] ℝ),‖f‖≤1 →
    let P:=WilsonOlderFreshSoftTrialCut.source R (D ∘ seat t) (d ∘ seat t) N K c S.draws S.paid κ pt cells y univ f
    let x:=fun i=>vector R d j K target η M Y before reg N per (seat t i)
    let h:=mass (d ∘ seat t) univ
    let H:=fun b=>cruises S.draws S.paid N h c w (P b)
    let full:=fun b=>cruises S.draws S.paid N h c v (P b)
    ∀q≤e,∀tval:ℝ,|tval|≤1 →
      (∏i,paid (seat t i))*‖reading R (d ∘ seat t) g x full q tval-WilsonOlderFreshSoftCoveredRead.cost R (d ∘ seat t) S.draws S.paid N w v q tval g x H‖≤
        bill R d (seat t) C*Real.exp (-ρ*s)

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(D:Fin 3→ℕ)(fit:∀i,grade i<D i)
    (e:ℕ)(A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀ᶠ v:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=v ∧
      ∀t:Finset (Fin 3),t.Nonempty → Hearing R grade D e v start V t A τ:=by
  let Faces:Type:={t:Finset (Fin 3)//t.Nonempty}
  choose floor purchased using fun h:Faces=>WilsonOlderFreshSoftTrialCut.original R simple shop grade (seat h.val)
    (D ∘ seat h.val) e univ (nonblank h.property) A τ a0 τ0
  let start:=∑h:Faces,floor h
  have earlier (h:Faces):floor h ≤ start:=single_le_sum (f:=floor) (fun _ _=>Nat.zero_le _) (mem_univ h)
  refine ⟨start,?_⟩
  filter_upwards [eventually_ge_atTop start,WilsonIndependentCollarCensusCourse.original paid 3 grade D fit e 0 0]
    with v onset appointment
  obtain ⟨V,draw,scheme,heat,anchor,_,_,shelf,_⟩:=appointment
  refine ⟨V,draw,scheme,heat,anchor,?_⟩
  intro t ht
  let h:Faces:=⟨t,ht⟩
  intro j paidJ N per K c w target vw wc cK KN vK warm window η M Y before reg η0 M0 income m C D₁ D₂ B ρ
  dsimp only
  intro p0 C0 salary stretch doses clip length κ pt cells y f probe q keep tval t1
  have law:LocalRatio V.paid:=scheme.symm ▸ (RunFormalChain.fromRun R).receipt
  have gradeIncome:Dormitory V (mass (grade ∘ seat t) univ) 0 Credit.leanC:=(population grade t).symm ▸ shelf t
  have visit:=purchased h v j ((earlier h).trans onset) (fun a=>(earlier h).trans (paidJ a))
    (fun a=>(paid.support (j a)).le) V anchor.le draw heat gradeIncome N per K c w target vw wc cK KN vK warm window
    η M Y before reg η0 M0 income m C D₁ D₂ B ρ p0 C0 salary stretch doses clip length κ pt cells y f probe q keep tval t1
  rw [←WilsonOlderFreshSoftCoveredRead.original R (grade ∘ seat t) V.draws V.paid simple law N
    (mass (grade ∘ seat t) univ) w v q vw ((wc.trans cK).trans KN.le) tval]
  exact visit

end YM.Integration.WilsonOlderFreshSoftRoseCourse
end
