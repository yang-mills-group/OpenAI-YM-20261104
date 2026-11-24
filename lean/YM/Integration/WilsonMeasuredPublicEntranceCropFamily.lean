import YM.Integration.WilsonMeasuredPublicEntranceCroppedPeer
import YM.Integration.WilsonMeasuredPublicEntrancePeerFace

/-! One tested finite family of real cropped peers with its original
addresses, exact numerical complement on every face, and individual tails. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCropFamily
open Finset Function Lattice Wilson RG Source Labels Marker QuadraticLocal PhysicalNext.Repeat Legato
open WilsonMeasuredPublicEntranceLampFamily WilsonOriginalDepositedRegularHearing
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V : Type} [DecidableEq V] [Fintype V] (J : Census V)
    {N p f : ℕ} (live : f≤N) (d : V→ℕ) (ref : ∀v,R.family.ref (d v)≤f)
    (o : V→Site (R.family.side f p)) (W : V→Rep G (R.family.side f p))
    (W' : Rep G (R.family.side f p))
    (q : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
    (D : V→ℕ)
local notation "P" => R.family.path.rep N p f

def value (v : V) (U : Config G (R.family.side f p)) : ℂ :=
  (q v).exponentialEntry (o v) (R.family.localSection (d v)) (W v) U-tail (W v) (q v) (D v) U

def fare (w M : V→ℝ) (v : V) :=
  WilsonOriginalStarPrimaryCatalog.rent R N p f (d v) o v (q v).x w (W'.p.supportExponent+2)+
    Real.exp (3*D v)*WilsonRetainedMarkedInletRegular.cost W'.p*(w v*M v)

include live ref in
theorem original (source : ∀v,(P).p=(W v).p) (target : W'.p=(P).p)
    (fit : ∀v,(q v).Format (o v) R.family.params (W v)) (w : V→ℝ) (wp : ∀v,0<w v)
    {κ M : V→ℝ} (fee : ∀v,(q v).remBound (o v) (W v) (κ v) (M v))
    (room : 1≤(P).p.supportExponent) :
    ∃ (A : V→Lamps Unit (Bool⊕ℕ) G W'.p o J) (I : Type) (_ : Countable I)
        (L : Lamps Unit I G W'.p o J),
      L.Paid w W'.p.B (W'.p.supportExponent+2) (∑v,fare (N:=N) R d o W' q D w M v) ∧
      (∀v,Kept W' o J (A v) L ∧ (A v).Paid w W'.p.B (W'.p.supportExponent+2) (fare (N:=N) R d o W' q D w M v) ∧
        (∀i,(A v).mode i=J.fire v) ∧ ∀U,((A v).log () U).part (J.fire v)=value R d o W q D v U) ∧
      (∀ U,L.log () U=∑v,Poly.send (J.fire v) (value R d o W q D v U)) ∧
      (∀v (s:J.Mode),v∈s.val→∀ U, WilsonMeasuredCompanionFace.peers L v s () U=
        ∏i∈s.val.erase v,value R d o W q D i U) ∧
      ∀ v U,‖(q v).exponentialEntry (o v) (R.family.localSection (d v)) (W v) U-
        value R d o W q D v U‖≤Real.exp (-(W v).p.supportExponent*D v)*M v := by
  classical
  choose A sale lane edge using fun v=>WilsonMeasuredPublicEntranceCroppedPeer.original R J live (ref v)
    o v (W v) W' (q v) (source v) target (fit v) w wp (D v) (fee v) room
  have read (v : V) (x : Unit) (U : Config G (R.family.side f p)) :
      ((A v).log x U).part (J.fire v)=value R d o W q D v U := (edge v U).1
  have pos : 0≤W'.p.supportExponent+2 := by rw [target]; linarith
  obtain ⟨I,count,L,bill,test,keys⟩ := WilsonMeasuredPublicEntranceLampFamily.original W' o J A w wp
    (W'.p.supportExponent+2) pos (fare (N:=N) R d o W' q D w M) sale lane
    (fun _ U v=>value R d o W q D v U) read univ
  refine ⟨A,I,count,L,bill,fun v=>⟨keys v (mem_univ _),sale v,lane v,read v ()⟩,test (),?_,?_⟩
  · intro v s hv U
    exact WilsonMeasuredPublicEntrancePeerFace.original L v s hv () U _ (test () U)
  · intro v U
    simpa only [←read v () U] using (edge v U).2

end YM.Integration.WilsonMeasuredPublicEntranceCropFamily
end
