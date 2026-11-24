import YM.Integration.WilsonPositionOriginalDressedQFactoredPair
import YM.Integration.WilsonRootedKioskPhysicalQExchange

/-! The earned original multi-Q return already includes the whole factored
mixed numerator needed for the reflected two-date Wilson test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPayout
open Lattice Wilson RG Marker QuadraticLocal WilsonRootedKioskOccupiedSlip
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V α ι:Type}[Fintype V][DecidableEq V]{Γ:Census V}
variable {P:Rep G n}{o:V→Site n}{w:V→ℝ}{k r fee hard maxCost low:ℝ}
variable (L:Lamps α ι G P.p o Γ)(Y:α → Config G n → Poly Γ)

omit [Fintype V] in
theorem mute (t:α)(U:Config G n):(bare L t U).part Γ.quiet=0:=by
  classical
  unfold WilsonRootedKioskOccupiedSlip.bare
  by_cases h:Summable (fun i=>Poly.send (L.mode i) (L.nominal t i U))
  · rw [Poly.share h]
    simp [Poly.part_send,fun i=>(L.live i).symm]
  rw [tsum_eq_zero_of_not_summable h,Poly.part_nil]

theorem original (Z:WilsonRootedKioskSealedPost.Return P o Γ w k r fee hard (bare L) Y)
    (a b:V)(apart:a≠b)(s:Γ.Mode)(roots:s.val={a,b})(t:α)(U:Config G n):
    (Y t U).part s-(Y t U).part (Γ.fire a)*(bare L t U).part (Γ.fire b)-
       (Y t U).part (Γ.fire b)*(bare L t U).part (Γ.fire a)+
       (P.eval U:ℂ)*(bare L t U).part (Γ.fire a)*(bare L t U).part (Γ.fire b)=
    (Z.output.density t U).part s+(P.eval U:ℂ)*(bare L t U).part s:=by
  have blank:(Y t U).part Γ.quiet=(P.eval U:ℂ):=by
    have e:=Z.quiet t U
    rw [Z.reading t U,Poly.quiet_mul,Poly.pass_part _ (by simp [mute L t U]),one_mul] at e
    exact e
  rw [←blank,Z.reading]
  exact WilsonPositionOriginalDressedQFactoredPair.original a b apart s roots _ _ (mute L t U)

theorem purchased (paid:WilsonRootedKioskMeasuredCourse.Payout («touch»:=o) P w k hard maxCost low (bare L) Y):
    ∃r fee:ℝ,r ≤ maxCost ∧ fee ≤ low ∧ ∃Z:WilsonRootedKioskSealedPost.Return P o Γ w k r fee hard (bare L) Y,
    ∀(a b:V),a≠b→∀s:Γ.Mode,s.val={a,b}→∀(t:α)(U:Config G n),
    (Y t U).part s-(Y t U).part (Γ.fire a)*(bare L t U).part (Γ.fire b)-
       (Y t U).part (Γ.fire b)*(bare L t U).part (Γ.fire a)+
       (P.eval U:ℂ)*(bare L t U).part (Γ.fire a)*(bare L t U).part (Γ.fire b)=
    (Z.output.density t U).part s+(P.eval U:ℂ)*(bare L t U).part s:=by
  obtain ⟨r,f,rh,fh,⟨Z⟩⟩:=paid
  exact ⟨r,f,rh,fh,Z,original L Y Z⟩

end YM.Integration.WilsonPositionOriginalDressedQPayout
