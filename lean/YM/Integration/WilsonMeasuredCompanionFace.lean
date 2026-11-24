import YM.Integration.WilsonMeasuredCompanionMount
import YM.Integration.WilsonPrecontactSeparatedLamps

/-! Restrict the real ordinary lamps to the spectator rows while raising the
tested entrant's radius, and restore the signed physical coefficient on its own vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionFace
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T ι:Type}[DecidableEq V]{J:Census V}{o:V→Site n}{W:Rep G n}
def wage (v:V)(w:V→ℝ)(a:ℝ)(i:V):ℝ:=if i=v then a else w i

/-- Retain any specified part of the original peer programme, on its original healthy masks. -/
theorem priced (E:Lamps T ι G W.p o J)(v:V)(w:V→ℝ)(a:ℝ)(peers:Set ι)
    (only:∀i∈peers,v∉(E.mode i).val){B:ℕ}{α C:ℝ}(paid:E.Paid w B α C):
    (WilsonPrecontactSeparatedLamps.portion E peers).Paid (wage v w a) B α C:=by
  let L:=WilsonPrecontactSeparatedLamps.portion E peers
  obtain ⟨f,hf,fit,sums⟩:=(WilsonPrecontactSeparatedLamps.charged E peers paid).budget
  refine ⟨f,hf,fit,?_⟩
  change Hit L.ground B (fun i=>Poly.toll (wage v w a) (L.mode i)*f i) α C
  have scales (i:peers):Poly.toll (wage v w a) (L.mode i)=Poly.toll w (L.mode i):=by
    apply prod_congr rfl
    intro j hj
    have ne:j≠v:=fun eq=>only i.val i.property (eq ▸ hj)
    exact if_neg ne
  simpa only [scales] using sums

variable [Fintype V]{d:ℕ}{F:Frame G d}{A:Hol G}
  {k κ B:ℝ}(rent:Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
  (v:V)(h:Coefficient F n)(fit:h.Format (o v) A W)(t:T→ℂ)
local notation "old" => (Hard.rent rent : Hard T W.p W.activities.forced W.activities.K o J)
local notation "raised" => joined (old) v h fit t

/-- Precisely the complementary ordinary coefficient that multiplies the new entrant. -/
def peers (E:Lamps T ι G W.p o J)(v:V)(s:J.Mode)(x:T)(U:Config G n):ℂ:=
  ((Poly.pass (E.log x U))*Poly.send (J.fire v) 1).part s

theorem on_field (E:Lamps T ι G W.p o J)(S:SectionData F)(w:V→ℝ)(positive:∀i,0<w i)
    (bound:∀x,‖t x‖≤1)(paid:h.remBound (o v) W κ B)(x:T)(s:J.Mode)(U:Config G n):
    t x*h.density (o v) S W U*peers E v s x U =
      t x*(soft h).density (o v) S W U*peers E v s x U+
      ((⟨E,(raised)⟩:Gallery T ι o W J).density x U).part s-
      ((⟨E,(old)⟩:Gallery T ι o W J).density x U).part s:=by
  have split:= congrArg (fun b:Poly J=>b.part s)
    (WilsonMeasuredCompanionMount.field rent v h fit t E w positive bound paid x U)
  have atom (z:ℂ): Poly.send (J.fire v) z = z • Poly.send (J.fire v) 1 :=by
    ext1 i
    rw [Poly.part_smul,Poly.part_send,Poly.part_send]
    split <;> simp
  rw [atom, mul_smul_comm] at split
  change ((⟨E,(raised)⟩:Gallery T ι o W J).density x U).part s-
      ((⟨E,(old)⟩:Gallery T ι o W J).density x U).part s=
      (t x*account h W U)*peers E v s x U at split
  have entire := (WilsonMeasuredOnlyHard.original h W W rfl rfl rfl S A (o v) κ B fit paid).2.2.1 U
  rw [entire]
  linear_combination -split

theorem fund (E:Lamps T ι G W.p o J)(w:V→ℝ)(positive:∀i,0<w i)
    (bound:∀x,‖t x‖≤1)(paid:h.remBound (o v) W κ B){C:ℝ}
    (cover:E.Paid w W.p.B W.p.supportExponent C):
    (⟨E,(old)⟩:Gallery T ι o W J).Pays w W.p.supportExponent C k ∧
    (⟨E,(raised)⟩:Gallery T ι o W J).Pays w W.p.supportExponent C (k+w v*(κ*B)):=by
  have base:=Hard.leasing (w:=w) rent (o:=o) (R:=J) (α:=T)
  exact ⟨⟨cover,base⟩,⟨cover,WilsonOriginalDepositedHard.paid (old) v h fit t w positive base bound paid⟩⟩

end YM.Integration.WilsonMeasuredCompanionFace
