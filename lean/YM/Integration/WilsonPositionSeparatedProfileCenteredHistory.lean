import YM.Integration.WilsonPositionSeparatedProfileCenteredPass

/-! Full ordered history of the same joint Wilson test at every genuine
fixed older observation scale, including the physical held identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredHistory
open Function Set MeasureTheory Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open RG05Readout.Harvest RG05Readout.Many RG05Readout.Records PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I] {N p n u:ℕ}

/-- The unnormalized density agrees on all held configurations, so it can
be propagated through arbitrary additional genuine lower kernels. -/
theorem earlier (D:I→ℕ) (v:(i:I)→Palette R.family (D i)) (r:ℝ) (Ψ:Wave I) (top:n+1≤N) {cap:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (m:ℕ)
    (regular:∀k (live:k≤N),timely (constellation (C:=R.family) (p:=p) D v r Ψ live m)) (old:u≤n):
    r*cap+2*R.family.S.a u<R.family.S.radius p →
    pulls R.family p N n 0 top (constellation D v r Ψ top m) u old=
      fun g=>dyes R.family u N p (old.trans (n.le_succ.trans top)) (constellation D v r Ψ (old.trans (n.le_succ.trans top)) m g):=by
  induction old using Nat.decreasingInduction with
  | self=>
    intro room;rw [Harvest.wakes top (constellation D v r Ψ top m)]
    funext g;exact WilsonPositionSeparatedProfileCenteredPass.cutoff R D v r Ψ top rp enclosed room m (regular _ top) g
  | of_succ k small ih=>
    intro room
    have longer:r*cap+2*R.family.S.a (k+1)<R.family.S.radius p:=by linarith only [room,R.family.S.strictAnti.antitone k.le_succ]
    rw [Harvest.down top (constellation D v r Ψ top m) small,ih longer]
    funext g;exact WilsonPositionSeparatedProfileCenteredPass.cutoff R D v r Ψ ((show k+1≤n from small).trans (n.le_succ.trans top)) rp enclosed room m (regular _ _) g

/-- At the true held unit, the complete lower `Harvest.pulls` is the
original conditional Wilson expectation of the full earlier constellation. -/
theorem held (D:I→ℕ) (v:(i:I)→Palette R.family (D i)) (r:ℝ) (Ψ:Wave I) (top:n+1≤N) {cap:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (m:ℕ)
    (regular:∀k (live:k≤N),timely (constellation (C:=R.family) (p:=p) D v r Ψ live m)) (old:u≤n)
    (room:r*cap+2*R.family.S.a u<R.family.S.radius p) (g:Body):
    pulls R.family p N n 0 top (constellation D v r Ψ top m) u old g 1/liftVac R.family.path N p u 1=
      dyes R.family u N p (old.trans (n.le_succ.trans top)) (constellation D v r Ψ (old.trans (n.le_succ.trans top)) m g) 1/liftVac R.family.path N p u 1:=by
  rw [earlier R D v r Ψ top rp enclosed m regular old room]

end YM.Integration.WilsonPositionSeparatedProfileCenteredHistory
