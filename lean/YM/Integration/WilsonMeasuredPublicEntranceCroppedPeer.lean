import YM.Integration.WilsonMeasuredPublicEntranceSoftHost

/-! The two true pre-test budgets buy the entire short regular particle on
either host. Changing its chart leaves the original long signed regular tail
with a pointwise exponential price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCroppedPeer
open Function Lattice RG Wilson Source Labels Marker QuadraticLocal
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonOriginalStarPrimaryCatalog WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow
open WilsonOriginalDepositedRegularHearing WilsonPhysicalMarkedDefect.RegularProjection
open WilsonThermometerHostedLamp
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {V : Type} [DecidableEq V] [Fintype V] (J : Census V)
    {N p f d : ℕ} (live : f≤N) (ref : R.family.ref d≤f)
    (o : V→Site (R.family.side f p)) (v : V)
    (W W' : Rep G (R.family.side f p))
    (q : Coefficient (R.family.labels.level d) (R.family.side f p))
local notation "P" => R.family.path.rep N p f

include live ref in
theorem original (source : (P).p=W.p) (target : W'.p=(P).p)
    (fit : q.Format (o v) R.family.params W) (w : V→ℝ) (wp : ∀v,0<w v)
    (D : ℕ) {κ M : ℝ} (fee : q.remBound (o v) W κ M)
    (room : 1≤(P).p.supportExponent) :
    ∃ L : Lamps Unit (Bool⊕ℕ) G W'.p o J,
      L.Paid w W'.p.B (W'.p.supportExponent+2)
        (rent R N p f d o v q.x w (W'.p.supportExponent+2)+
          Real.exp (3*D)*WilsonRetainedMarkedInletRegular.cost W'.p*(w v*M)) ∧
      (∀l,L.mode l=J.fire v) ∧
      ∀ U, (L.log () U).part (J.fire v) = q.exponentialEntry (o v) (R.family.localSection d) W U-
        WilsonOriginalDepositedRegularHearing.tail W q D U ∧
        ‖q.exponentialEntry (o v) (R.family.localSection d) W U-(L.log () U).part (J.fire v)‖ ≤
          Real.exp (-W.p.supportExponent*D)*M := by
  classical
  rw [target]
  obtain ⟨legal,cash,value⟩ := WilsonMeasuredPublicEntranceSoftHost.original q W P source
    (o v) R.family.params (R.family.localSection d) fit fee
  let tag := fun _ : Unit => (1:ℂ)
  let included := small (P) (soft q) D
  refine ⟨enrolled (J:=J) R live ref o v (soft q) legal tag included,?_,?_,?_⟩
  · exact cropped R live ref o v (soft q) legal tag w wp (by simp [tag]) cash D
  · exact modes R live ref o v (soft q) legal tag included
  · intro U
    have span := whole (J:=J) v (soft q) legal tag D w wp (by simp [tag]) cash room () U
    have outside := WilsonOriginalStarIncomingRead.omitted (J:=J) v (soft q) legal tag D w wp
      (by simp [tag]) cash room () U
    rw [outside] at span
    simp only [tag,one_mul] at span
    have inside := (short (J:=J) v (soft q) legal tag D w wp (by simp [tag]) cash).sums (by linarith) wp () U
    have tail_eq : tail (P) (soft q) D U=tail W q D U := by
      simp only [tail,rejected,small,Coefficient.maskedTerm,soft,source]
    have eq : ((enrolled (J:=J) R live ref o v (soft q) legal tag included).log () U).part (J.fire v)=
        q.exponentialEntry (o v) (R.family.localSection d) W U-tail W q D U := by
      rw [enrolled,Lamps.joinLog _ _ Summable.of_finite inside,Poly.part_plus,filed,←value,←tail_eq]
      simp only [tag,one_mul]
      change _+_=(primary R N p f d o v (soft q).x U+∑' l,(soft q).maskedTerm (P) l U)-tail (P) (soft q) D U
      linear_combination span
    refine ⟨eq,?_⟩
    rw [eq,sub_sub_cancel]
    exact WilsonOriginalDepositedRegularHearing.price W q D fee U

end YM.Integration.WilsonMeasuredPublicEntranceCroppedPeer
end
