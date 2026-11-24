import YM.Integration.WilsonOriginalStarPrimaryCatalog
import YM.Integration.WilsonOriginalDepositedRegularWindow
import YM.Integration.WilsonOriginalDepositedRegularHearing

/-! Literal regular function of a canonical original color in an admissible gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerHostedLamp
open Function Filter Finset Lattice Wilson RG Source Labels Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open Next.Foundations Push.Local PhysicalNext PhysicalNext.Repeat Legato
open WilsonOriginalStarPrimaryCatalog WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow
open WilsonRetainedMarkedInletRegular
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {V T:Type} [DecidableEq V] [Fintype V] {J:Census V}
  {N p j d:ℕ} (live:j≤N) (ref:R.family.ref d≤j)
  (o:V→Site (R.family.side j p)) (v:V)
variable (q:Coefficient (R.family.labels.level d) (R.family.side j p)) (fit:q.Format (o v) R.family.params (R.family.path.rep N p j))
  (t:T→ℂ)

def enrolled (keep:ℕ→Prop):Lamps T (Bool⊕ℕ) G (R.family.path.rep N p j).p o J:=
  (WilsonOriginalStarPrimaryCatalog.catalogue (J:=J) R N p j d live ref o v q.x t).join
    (WilsonOriginalDepositedRegular.lamps (J:=J) v q fit t keep)

omit [Fintype V] in
theorem modes (keep:ℕ→Prop) (l:Bool⊕ℕ):(enrolled (J:=J) R live ref o v q fit t keep).mode l=J.fire v:=by
  cases l <;> rfl

variable (w:V→ℝ) (pos:∀i,0<w i) (bound:∀x,‖t x‖≤1) {κ B:ℝ} (fee:q.remBound (o v) (R.family.path.rep N p j) κ B)
include pos bound fee in
theorem complete :
  (enrolled (J:=J) R live ref o v q fit t (fun _=>True)).Paid w (R.family.path.rep N p j).p.B ((R.family.path.rep N p j).p.supportExponent-1)
    (rent R N p j d o v q.x w ((R.family.path.rep N p j).p.supportExponent-1)+cost (R.family.path.rep N p j).p*(w v*B)):=by
  have reg:=WilsonOriginalDepositedRegular.paid (J:=J) v q fit t (fun _=>True) w pos bound fee (by norm_num:0≤(1:ℝ))
    (a:=(R.family.path.rep N p j).p.supportExponent-1) (fun _ _=>by rw [one_mul])
  simpa only [one_mul] using! Lamps.joinPaid
    (WilsonOriginalStarPrimaryCatalog.funded (J:=J) R N p j d live ref o v q.x t w pos ((R.family.path.rep N p j).p.supportExponent-1) bound) reg

include pos bound fee in
theorem cropped (D:ℕ) :
  (enrolled (J:=J) R live ref o v q fit t (small (R.family.path.rep N p j) q D)).Paid w (R.family.path.rep N p j).p.B ((R.family.path.rep N p j).p.supportExponent+2)
    (rent R N p j d o v q.x w ((R.family.path.rep N p j).p.supportExponent+2)+Real.exp (3*D)*cost (R.family.path.rep N p j).p*(w v*B)):=by
  exact Lamps.joinPaid (WilsonOriginalStarPrimaryCatalog.funded (J:=J) R N p j d live ref o v q.x t w pos _ bound)
    (WilsonOriginalDepositedRegularWindow.short (J:=J) v q fit t D w pos bound fee)

theorem field (keep:ℕ→Prop) (x:T) (U:Config G (R.family.side j p))
    (hs:Summable (fun l=>(WilsonOriginalDepositedRegular.lamps (J:=J) v q fit t keep).frame l x U)) :
    ((enrolled (J:=J) R live ref o v q fit t keep).log x U).part (J.fire v)=
     t x*(q.x 0+masked (R.family.path.rep N p j).p.threshold ((R.family.localSection d).footprint (o v))
       ((R.family.localSection d).places ((R.family.labels.level d).scaled (R.family.path.rep N p j).p.threshold⁻¹ ((R.family.labels.level d).core q.x)) (o v)) U+
       ∑'l,(if keep l then q.maskedTerm (R.family.path.rep N p j) l U else 0)):=by
  rw [enrolled,Lamps.joinLog _ _ Summable.of_finite hs,Poly.part_plus,
    WilsonOriginalStarPrimaryCatalog.filed,Lamps.log,Poly.share hs]
  simp only [WilsonOriginalDepositedRegular.row,Poly.part_send,↓reduceIte]
  have vals (l:ℕ): (if keep l then t x else 0)*q.maskedTerm (R.family.path.rep N p j) l U =
    t x*(if keep l then q.maskedTerm (R.family.path.rep N p j) l U else 0):=by by_cases h:keep l <;> simp [h]
  simp_rw [vals]
  rw [tsum_mul_left]
  change t x*(_+_) + t x*_ = t x*((_+_)+_)
  rw [←mul_add]
  rfl

include pos bound fee in
theorem full (wide:1≤(R.family.path.rep N p j).p.supportExponent) (x:T) (U:Config G (R.family.side j p)):
    ((enrolled (J:=J) R live ref o v q fit t (fun _=>True)).log x U).part (J.fire v)=
       t x*q.exponentialEntry (o v) (R.family.localSection d) (R.family.path.rep N p j) U:=by
  have reg:=WilsonOriginalDepositedRegular.paid (J:=J) v q fit t (fun _=>True) w pos bound fee (by norm_num:0≤(1:ℝ))
    (a:=(R.family.path.rep N p j).p.supportExponent-1) (fun _ _=>by rw [one_mul])
  simpa only [if_true,Coefficient.exponentialEntry] using
    field (J:=J) R live ref o v q fit t (fun _=>True) x U (reg.sums (by linarith) pos x U)

end YM.Integration.WilsonThermometerHostedLamp
