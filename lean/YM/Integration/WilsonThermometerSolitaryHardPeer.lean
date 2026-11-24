import YM.Integration.WilsonOriginalOneColorGallery
import YM.Integration.WilsonThermometerOccupiedGallery
import YM.Integration.WilsonMeasuredCompanionFace

/-! An occupied hard singleton tested against the other actual ordinary seats of a three-field post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryHardPeer
open Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached RG3.Letters
open WilsonOriginalOneColor
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {J:Census V} {o:V→Site n} {W:Rep G n}
variable {T ι I:Type}

def withPeers (A:Gallery T ι o W J)(v:V)(E:Lamps T I G W.p o J):Gallery T I o W J:=
  ⟨E,hard v A.K⟩

omit [Fintype V] in
theorem cut_shape (v:V)(a:Poly J):
    cut v a=Poly.bead J (a.part J.quiet)+Poly.send (J.fire v) (a.part (J.fire v)):=by
  ext1 s
  rw [part,Poly.part_plus]
  simp only [Poly.bead,Poly.part_send]
  by_cases empty:s=J.quiet
  · subst s
    simp [visible,Census.quiet,Census.fire]
  by_cases eq:s=J.fire v
  · subst s
    simp [visible,Census.quiet,Census.fire]
  have off:¬visible v s:=by
    intro vis
    apply eq
    have active:s.val.Nonempty:=by
      apply Finset.nonempty_iff_ne_empty.mpr
      exact fun h=>empty (Subtype.ext h)
    obtain ⟨i,hi⟩:=active
    have same:=mem_singleton.mp (vis hi)
    exact Subtype.ext (Finset.Subset.antisymm vis (singleton_subset_iff.mpr (same ▸ hi)))
  simp [off,empty,eq]

omit [Fintype V] in
theorem send_unit (j:J.Mode)(c:ℂ):Poly.send j c=c • Poly.send j (1:ℂ):=by
  ext1 s
  simp only [Poly.part_send,Poly.part_smul]
  split <;> simp

/-- Every originally compatible quiet term is still present in the scalar multiplying the peers. -/
theorem field (A:Gallery T ι o W J)(v:V)(E:Lamps T I G W.p o J)(x:T)(U:Config G n)
    (sm:Summable (packet W.activities W.p (A.K.hard x) U)):
    ((withPeers A v E).density x U)-(W.eval U:ℂ) • Poly.pass (E.log x U)=
      ((Real.exp (W.exponent U):ℂ)*(A.gas x U).part (J.fire v)) •
        (Poly.pass (E.log x U)*Poly.send (J.fire v) 1):=by
  have g:(withPeers A v E).gas x U=cut v (A.gas x U):= WilsonOriginalOneColorGallery.gas v A x U sm
  have quiet:(A.gas x U).part J.quiet=(W.activities.gas W.p U:ℂ):=Hard.packet_of_quiet A.K x U sm
  rw [cut_shape,quiet] at g
  rw [Gallery.density,g]
  change (Real.exp (W.exponent U):ℂ) • (Poly.pass (E.log x U)*(_+_))-_=_
  rw [mul_add,smul_add,mul_comm _ (Poly.bead _ _),Poly.product_bead,smul_smul]
  rw [Rep.eval,Complex.ofReal_mul,add_sub_cancel_left,send_unit,mul_smul_comm,smul_smul]

theorem mode (A:Gallery T ι o W J)(v:V)(E:Lamps T I G W.p o J)(x:T)(U:Config G n)(s:J.Mode)
    (sm:Summable (packet W.activities W.p (A.K.hard x) U)):
    ((withPeers A v E).density x U).part s-(W.eval U:ℂ)*(Poly.pass (E.log x U)).part s=
      ((Real.exp (W.exponent U):ℂ)*(A.gas x U).part (J.fire v))* WilsonMeasuredCompanionFace.peers E v s x U:=by
  have h:=congrArg (fun p:Poly J=>p.part s) (field A v E x U sm)
  simpa only [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,Poly.part_smul,WilsonMeasuredCompanionFace.peers] using h

end YM.Integration.WilsonThermometerSolitaryHardPeer
