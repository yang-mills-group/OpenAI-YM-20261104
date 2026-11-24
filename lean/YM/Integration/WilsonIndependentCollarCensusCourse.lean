import YM.Integration.WilsonIndependentCollarCensusAppointment

/-! The whole connected census and the optical trajectory cache are issued by
one tokenizer on the same physically funded, before-cutoff school. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCensusCourse
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
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

def Law {e:ℕ}(V:Realm G (e+1) Credit.leanC):Prop:=
  ∀m (hm:V.anchor ≤ m),let U:=V.mint m hm
    U.σ≤1 ∧ U.gear.s=2*U.σ ∧ 2*elixir U.gear=3*U.σ

def Fees {n e:ℕ}(R:Run G)(V:Realm G (e+1) Credit.leanC)(s:WilsonOriginalAllOrderCourse.Schedule G)(k:Fin n→ℕ):Prop:=
  let L:=R.family.path.levels
  ∀ᶠm:ℕ in atTop,∀hm:V.anchor ≤ m,∀J:Finset (Fin n),
    let j:=L.clock.J (m+1)
    let w:=widths (teacher (prepared s)) j
    let out:=WilsonIndependentCollarPrintIncome.issue w (e+1) (mass k J) (V.mint m hm).gear
    out.fee≤V.y m ∧ out.strip⁻¹≤V.y m ∧
      ∀x,x=L.clock.J m ∨ x=j → teacherWidth (teacher (prepared s)) R.metals.p.kernel x≤out.strip

def Appointed {n e:ℕ}(R:Run G)(simple:G.Simple)(V:Realm G (e+1) Credit.leanC)
    (s:WilsonOriginalAllOrderCourse.Schedule G)(D k:Fin n→ℕ):Prop:=
  let L:=R.family.path.levels
  let req:=teacher (prepared s)
  let R₀:=WilsonOlderFreshGraphSchool.roots (menu req) simple R.metals.p R.metals.K
  ∀δ:ℝ,0<δ → ∀ᶠm:ℕ in atTop,∀(hm:V.anchor ≤ m)(ψ:ℕ→ℕ)(K x:ℕ),
    1≤K → n≤K → (x=L.clock.J m ∨ x=L.clock.J (m+1)) →
    WilsonOlderFreshConnectedAppointment.Paid R V hm D k δ (Poetry.Agenda.seed R₀ ψ K x)

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(k D:Fin n→ℕ)(hk:∀x,k x<D x)(e b h:ℕ):
    let L:=R.family.path.levels
    ∀ᶠfirst:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=L ∧ V.paid=R.metals.O ∧ V.y=zz L ∧ V.anchor=first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      (∀J:Finset (Fin n),Dormitory V (mass k J) 0 Credit.leanC) ∧
      Law V ∧ Fees R V s k ∧ Appointed R simple V s D k:=by
  intro L
  filter_upwards [WilsonOriginalOpticalMint.original paid n k D hk e b h (mass k univ)] with first invoice
  obtain ⟨V,draw,chart,clock,anchor,school,sale,_,dorm,opens⟩:=invoice
  have law:Law V:=by
    intro m hm
    obtain ⟨j,mark,twice,radial,_⟩:=opens m hm
    exact ⟨mark.le.trans (WilsonIndependentCollarOpticalElected.top_width _ _ j),twice,radial⟩
  have fees:Fees R V s k:=by
    dsimp only [Fees]
    have fit:=(L.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (max (e+1) (mass k univ))
    filter_upwards [fit] with m stage
    intro hm J
    have seats:mass k J ≤ mass k univ:=by rw [stairK k (subset_univ J)];exact Nat.le_add_right ..
    obtain ⟨_,_,_,_,_,_,_,printed⟩:=opens m hm
    obtain ⟨fee,strip,_,_,choice⟩:=printed (e+1) (mass k J) ((le_max_left ..).trans stage) (seats.trans ((le_max_right ..).trans stage))
    rw [clock];exact ⟨fee,strip,choice⟩
  refine ⟨V,draw,chart,clock,anchor,school,sale,fun J=>dorm (mass k J) 0 ?_ (Nat.zero_le _),law,fees,?_⟩
  · rw [stairK k (subset_univ J)];exact Nat.le_add_right ..
  dsimp only [Appointed]
  intro δ hp
  filter_upwards [fees,WilsonIndependentCollarCensusAppointment.original R simple D k V clock school hp] with m hired appointment
  intro hm ψ K x work enough near
  have current:=law m hm
  exact appointment hm (widths (teacher (prepared s)) (L.clock.J (m+1))) (teacher (prepared s)) ψ K x work enough
    current.2.1 current.1 fun J=>⟨(hired hm J).1,(hired hm J).2.1,(hired hm J).2.2 x near⟩

end YM.Integration.WilsonIndependentCollarCensusCourse
end
