import YM.Integration.WilsonThermometerUnitFilingMomentPanel
import YM.Integration.WilsonOlderFreshGraphArmada
/-! On the unary compound every original row has the same lifted source site
at its specified copy. Thus the rooted moment salary hears the complete
signed covered field on that copy, retaining the same tested chart. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinnedIncome
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalNamedRelativeRows WilsonOriginalRelativeMixedFields
open WilsonOriginalSuspendedFootprint WilsonOriginalJointDeckMotion WilsonEmittedRootedJetWage
open WilsonThermometerUnitFilingMomentPanel
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {o:Passport n Unit} {J:Census Unit} {I X:Type}
  (h:n.val∣N.val) (M:I → Row o J G X) (p:Fin (Pages n N))
local notation "active" => J.fire ()
def locus (o:Passport n Unit):Site N:=(page h (o.origin ()) p).val

def envelope (t:X) (j:ℕ)(z:Joint G N):ℂ:=
  (z.1^j:ℝ)*WilsonOriginalMixedCoveredRead.field h M t p (fun _=>True) z

def slots (s:Finset Unit)(r:ℕ): (Fin r → Slot G N) ↪ Choice s n N G r where
  toFun v:=(p,fun _=>p,v)
  inj':=by intro a b h;exact congrArg (fun w:Choice s n N G r=>w.2.2) h

theorem place (T:Row o J G X):
    (row h T p).center=locus h p o ∧ ∀v:Unit,index h T p v=p:=by
  have C:T.center=o.origin ():=congrArg o.origin (Subsingleton.elim T.binder.front ())
  have here:(row h T p).center=locus h p o:=by rw [centered];unfold anchor locus;rw [C]
  refine ⟨here,?_⟩
  intro v
  cases v
  have G:=active_page h T p ()
  have first:()=T.binder.front:=Subsingleton.elim .. 
  unfold site at G
  rw [if_pos first] at G
  unfold anchor at G;rw [C] at G
  exact (page h (o.origin ())).injective (Subtype.ext G)

theorem selected_on (r:ℕ)(y:Fin r → Slot G N)(z:I):
    selected h M (active) (locus h p o) (slots (G:=G) p (active).val r y) z:=by
  refine ⟨Subtype.ext ?_,(place h p (M z)).1,?_⟩
  · have full:=WilsonOlderFreshGraphArmada.full_mode (M z).binder
    change (M z).mode.val={ () }
    rw [full];ext v;cases v;simp
  · funext v;exact (place h p (M z)).2 v.val

theorem field (t:X)(j r:ℕ)(y:Fin r → Slot G N):
    joined h M t (active) (locus h p o) j (slots (G:=G) p (active).val r y)=envelope h M p t j:=by
  funext z
  unfold joined envelope
  have eq:(selected h M (active) (locus h p o) (slots (G:=G) p (active).val r y))=(fun _:I=>True):=by
    funext i;exact propext (iff_true_intro (selected_on h M p r y i))
  rw [eq];rfl

def premium (o:Passport n Unit) (a:ℕ) {r:ℕ} (y:Fin r → Slot G N):ℝ:=
  (1+2*(WilsonOriginalCenteredSeamSalary.radius (locus h p o) (trace y ∪ {locus h p o}):ℝ))^a

theorem charged {w:Unit → ℝ} {grades:Unit → ℕ}{σ C:ℝ}{ord cap H:ℕ}
    (stock:Scene.Armada M w grades σ C ord cap H){β δ:ℝ}(seed:0<σ)(tiny:0<δ)
    (late:Real.exp 1 ≤ β)(paid:Real.exp (σ⁻¹^2) ≤ β)(t:X)(j r a:ℕ)(test:Finset (Fin r → Slot G N)):
    w () * ∑y∈test,premium h p o a y * ‖entry r (envelope h M p t j) y‖ ≤ 
      WilsonThermometerUnitFilingMomentSale.price G r a δ * β^δ*C:=by
  have bill:=WilsonThermometerUnitFilingMomentPanel.original h M stock seed tiny late paid t
    (active) (locus h p o) j r a (test.map (slots p (active).val r))
  have single:rootset h o (active).val (fun _=>p)={locus h p o}:=by
    ext u
    simp only [rootset,mem_image,mem_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨z,rfl⟩;rfl
    · rintro rfl
      refine ⟨⟨(),?_⟩,rfl⟩
      simp [Census.fire]
  rw [sum_map] at bill
  have toll:Poly.toll w (active)=w ():=by simp only [Poly.toll,Census.fire,prod_singleton]
  rw [toll] at bill
  convert bill using 1
  congr 1
  apply sum_congr rfl
  intro y _
  unfold payment premium
  rw [field h M p t j r y]
  change _=(1+2*(WilsonOriginalCenteredSeamSalary.radius (locus h p o)
    (trace y ∪ rootset h o (active).val (fun _=>p)):ℝ))^a*_
  rw [single]
  rfl

end YM.Integration.WilsonThermometerUnitFilingPinnedIncome
