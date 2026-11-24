import YM.Integration.WilsonOriginalGalleryTwinWalk
import YM.Integration.WilsonMeasuredCompanionFace
import YM.Integration.WilsonMeasuredOwnerReserve
import YM.Integration.WilsonPrecontactSeparatedLamps
import YM.QuadraticLocal.Tariff.Measure

/-! Both signed alternatives use the earning canonical Wilson gallery, on every group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionTwinIntake
open MeasureTheory Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal QuadraticLocal.Earn
open AbsoluteSums Labels Source MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout.Many RG05Readout.Address QuadraticLocal.Fusion.Attached Lodestar
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonOriginalDepositedHard WilsonOriginalGalleryTwins
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V][Countable I]
  {P:Rep G n}{o:V→Site n}{dec amt safe tilt heat:ℝ}
local notation "J" => Stock.census V
omit [Countable I] in
private theorem hard_le (H:Hard T P.p P.activities.forced P.activities.K o (J))
    {w:V→ℝ}(wp:∀i,0<w i){a a' b:ℝ}(le:a≤a')(paid:H.Paid w P.p.B a' b):
    H.Paid w P.p.B a b:=by
  obtain ⟨f,hf,hit⟩:=paid.wages
  refine ⟨f,hf,fun i=>budget_mono (hit i) ?_ ?_⟩
  · intro j
    split
    · exact mul_nonneg (Poly.nonnegative wp _) (Real.exp_nonneg _)
    · rfl
  · intro j
    split
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right le (Nat.cast_nonneg _))) (Poly.nonnegative wp _)
    · rfl

def Admitted (D:Gallery T I o P (J))(x:T)(w:V→ℝ)(a:ℝ):Prop:=
  D.E.Paid (fun i=>w i^2) P.p.B a 1 ∧ D.K.Paid (fun i=>w i^2) P.p.B a 1 ∧
    Integrable (D.density x) (prior G n) ∧
    MenuBoard P (fun _:V×Bool=>(0:Three G n)) (entered D x) (o ∘ Prod.fst) (w ∘ Prod.fst) a 1

private theorem board (D:Gallery T I o P (J))(x:T)(w:V→ℝ)(positive:∀i,0<w i)
    (law:P.Lawful dec amt safe tilt heat){a:ℝ}(expo:0≤a)(within:a≤P.p.supportExponent)
    (bill:D.Pays (fun i=>w i^2) P.p.supportExponent 1 1):
    Admitted D x w a:=by
  let w₂ := fun i=>w i^2
  have wp(i):0<w₂ i:=pow_pos (positive i) _
  have actual:=QuadraticLocal.Tariff.integrable (J) o w₂ wp D x bill P.p.exponent_pos.le law
  have old:=WilsonPrecontactSeparatedLamps.lower D.E within wp bill.1
  have hard:=hard_le D.K wp within bill.2
  exact ⟨old,hard,actual,WilsonOriginalGalleryTwinBoard.original D x w positive expo old hard actual⟩

variable {d:ℕ}{F:Frame G d}{A:Hol G}{k κ B:ℝ}
  (rent:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
  (v:V)(h:Coefficient F n)(fit:h.Format (o v) A P)(S:SectionData F)(t:T→ℂ)
local notation "old" => (Hard.rent rent : Hard T P.p P.activities.forced P.activities.K o (J))
local notation "fresh" => joined (old) v h fit t

/-- The trials, their tolls and their physical source share every incumbent key of this P. -/
theorem received (E:Lamps T I G P.p o (J))(w:V→ℝ)(positive:∀i,0<w i)
    (law:P.Lawful dec amt safe tilt heat)(bound:∀x,‖t x‖≤1)(inc:h.remBound (o v) P κ B)
    (cash:k≤1)(room:k+w v^2*(κ*B)≤1)
    (regular:E.Paid (fun i=>w i^2) P.p.B P.p.supportExponent 1)
    {a:ℝ}(expo:0≤a)(within:a≤P.p.supportExponent)(x:T):
    let L₀:= (⟨E,(old)⟩:Gallery T I o P (J))
    let L₁:= (⟨E,(fresh)⟩:Gallery T I o P (J))
    Admitted L₀ x w a ∧ Admitted L₁ x w a ∧
      clear L₀ x=clear L₁ x ∧ ∀(s:(J).Mode)(U:Config G n),
      t x*h.density (o v) S P U*WilsonMeasuredCompanionFace.peers E v s x U=
        t x*(soft h).density (o v) S P U*WilsonMeasuredCompanionFace.peers E v s x U+
        (L₁.density x U).part s-(L₀.density x U).part s:=by
  let w₂:=fun i=>w i^2
  have wp(i):0<w₂ i:=pow_pos (positive i) _
  obtain ⟨lo,hi⟩:=WilsonMeasuredCompanionFace.fund rent v h fit t E w₂ wp bound inc regular
  refine ⟨board _ x w positive law expo within ⟨lo.1,Hard.mono _ lo.2 cash⟩,
    board _ x w positive law expo within ⟨hi.1,Hard.mono _ hi.2 room⟩,rfl,?_⟩
  intro s U
  exact WilsonMeasuredCompanionFace.on_field rent v h fit t E S w₂ wp bound inc x s U

end YM.Integration.WilsonOriginalCompanionTwinIntake
