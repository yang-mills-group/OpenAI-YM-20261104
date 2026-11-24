import YM.Integration.WilsonOlderSignedSingletonFare
import YM.QuadraticLocal.Tint.Patrol

/-! Install the entire incoming one-source table, including that table's own analytic and hard entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareGallery
open Function Finset Lattice Wilson RG Marker QuadraticLocal Ac QuadraticLocal.Earn Extra.Histories Extra.Trajectories
open Source Labels Push.Local Planned.GuardedAtom WilsonCenteredFiledAtoms
open Push Push.AbsoluteSums RemainderComparison ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {α ι J V:Type} [DecidableEq V] [Fintype V]
  {P:Earn.Passport n V} {R:Census V} {W:Rep G n}
  (model:ι→Earn.Row P R G α) (I:Tint.Incoming P W α J R)
  (w:V→ℝ) (grades:V→ℕ) {d:ℕ} {F:Frame G d}

theorem issued {σ θ ζ gross κ μ η C Λ δ h:ℝ} {k s u:ℕ}
    (salary:Earn.Scene.Armada model w grades σ gross k s u)
    (wallet:Invoice.Supports W.p h (W.p.supportExponent+2) (Coat.gStep W.beta) σ θ)
    {old force:ℝ} (regular:I.old.Paid w W.p.B (W.p.supportExponent+2) old)
    (hard:I.hard.Paid w W.p.B W.p.supportExponent force)
    (K:Guard.Keeper W.p W.activities) (law:W.Lawful ζ C Λ δ η)
    (positive:0<κ) (pos:0≤η) (room:hitWidth W.p*η≤1)
    (S:SectionData F) (Y:Hol G) (readable:Readable Y S W.p n μ)
    (v:V) (t:α) (z:ℂ) :
    let y:=P.origin v
    let ap:=Invoice.price W.p h (k+u+1) s (W.p.supportExponent+2) θ G
    Store W S Y y κ
      (WilsonOlderSignedSingletonFare.fare W.p S Y w (R.fire v) z {y} 0 (ap*gross+old) force κ η μ)
      (fun U=>z*((Tint.Patrol.picture model I).density t U).part (R.fire v)) :=by
  let a:=Earn.Scene.Armada.paid model w grades salary W.p wallet
  have hreg:(Tint.Patrol.picture model I).E.Paid w W.p.B (W.p.supportExponent+2)
      (Invoice.price W.p h (k+u+1) s (W.p.supportExponent+2) θ G*gross+old):=
    Lamps.joinPaid a regular
  apply WilsonOlderSignedSingletonFare.original (Tint.Patrol.picture model I) t v z w salary.positive
    hreg hard positive pos room W.p.exponent_pos.le law K {P.origin v} (P.origin v)
    (Finset.mem_singleton_self _) (Finset.mem_singleton_self _) 0 _ S Y readable
  exact (separation_self _).le
end YM.Integration.WilsonOriginalNullBareGallery
