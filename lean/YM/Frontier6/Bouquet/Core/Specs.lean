import YM.Frontier6.Bouquet.Meter.Transport
import YM.Frontier6.Prescription.Report

/-! Clock labels for the recursive local rule. All quantities depend only on
 original arity grades, not which exterior future is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble} (i:P)
variable (d:Slot→ ℕ)
namespace Pod
def arityD (p:Pod)(d:Slot→ℕ): ℕ:= ∑ i∈p.val,d i
def horizon (p:Pod)(d:Slot→ℕ): ℕ:= tiers (normal p) (p.arityD d) -- check import
abbrev Horizon (p:Pod)(d:Slot →ℕ):= Fin (p.horizon d)
def track (p:Pod)(w:Fin (p.horizon d)) : ℕ:=kilo (normal p) (p.arityD d) w
end Pod
-- `strike` as cumulative on the whole algebraic measure space. No observer
-- outside visibility, but globally linear with this totalization. `advance` is
-- the signed continuation `$1 - \text{strike}(\ldots)`. (Input grades stay.)
variable (z:E4)(b:ℕ)
def strike : Spelling S →ₗ[ℂ] Spelling S:=∑ i: Fin b, stagePart K z i.val
def advance : Spelling S →ₗ[ℂ] Spelling S:= LinearMap.id-strike K z b
lemma advance_value (f:Spelling S):advance K z b f=f-∑ i:Fin b,stagePart K z i f:=by unfold advance strike; rw [LinearMap.sub_apply, LinearMap.id_apply,LinearMap.sum_apply]
lemma advance_high {b:ℕ}{f:Spelling S}(he:Visible K z b f): advance K z (b+1) f= Forest.reject K z b f:=by
   unfold Forest.reject; rw [advance_value, all_from_parts K _ _ _ he]; congr 1; exact Finset.sum_congr rfl (fun i _=> stage_part K _ (he.low K (Nat.lt_add_one_iff.mp i.isLt)))
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
    (x: Seats P) (H J:Patron S P Y) (f g:Full (fiber P))(s:ℝ)
def key (i:P) (x:Seats P)(w:ℕ): Patron S P Y := transaction H i (stagePart K (x i) w)
def main (i:P) (d:Slot→ℕ) (x:Seats P) : Patron S P Y:= transaction H i (advance K (x i) (i.val.horizon d))
def atBook (i:P)(d: Slot→ ℕ)(t:ℝ)(w: i.val.Horizon d): Tandem.Essay (fiber P):= page (home_sub (P:=P) i.property) t (i.val.track d w)
abbrev overBook (i:P)(d: Slot→ ℕ)(t:ℝ)(w: i.val.Horizon d): Tandem.Essay (fiber P):= escape (home_sub (P:=P) i.property) t (i.val.track d w)
lemma overBook_eq (w:i.val.Horizon d): overBook i d s w f= f-atBook i d s w f:=rfl
lemma main_eq (f:Program S P): main K H i d x f=H f-∑ w:i.val.Horizon d, key K H i x w f:=by
    unfold main key; simp_rw [ticket, advance_value,map_sub,map_sum]; rw [show H.toLinearMap f i (f i)=H f by change H (Function.update f i (f i))= _; rw [update_eq_self]] -- name
lemma frontage : main K H i d x+(∑ w:i.val.Horizon d, key K H i x w)=H:=by ext1 f; rw [add_apply, main_eq, _root_.sum_apply, sub_add_cancel] -- add_apply disamb

-- Root-only protocol clause (build this for universal Probe $Teller` from exact data)
abbrev Payroll (p:Pod)(K:Final C F S)(d:Slot→ℕ)(s:ℝ)(A:Teller S)(T:Veins):Prop :=
    ∀ {Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
      (x: Seats (only p)) (H:Patron S (only p) Y)(f: Full (fiber (only p)))(i:only p), marble K A T i x H f= - (∑ w:i.val.Horizon d,pollen K A T i x (key K H i x w) (atBook i d s w f))
end YM.Frontier6.Bouquet
