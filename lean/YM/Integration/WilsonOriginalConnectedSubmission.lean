import YM.Integration.WilsonOriginalMixedBlockTable
import YM.Integration.WilsonRootedKioskCompleteFiling

/-! Enumerating all genuine connected faces reproduces the original square-free table.
The reporting root of each face is taken from that face itself, before the test or field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalConnectedSubmission
open Function Finset Lattice Wilson RG Marker Multi Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators

variable {V:Type} [Fintype V] [DecidableEq V] {J:Census V}

def address {n:Side} (p:Earn.Passport n V)(s:Hot J):Earn.Binder p J where
  mode:=s.val
  front:=s.property.choose
  east:=s.property.choose_spec
  path v:=Earn.Cable.link (p.origin s.property.choose) (p.origin v)
  span _ _:=Earn.Cable.link_stop _ _
  extra:=0

omit [Fintype V] in
theorem length {n:Side} (p:Earn.Passport n V)(s:Hot J):(address p s).length=
    ∑v∈s.sites, ((Earn.Cable.link (p.origin s.property.choose) (p.origin v)).length+p.height v):=by
  simp [address,Earn.Binder.length,Earn.Binder.distance]

omit [Fintype V] in
theorem sum (L:Poly J)(quiet:L.part J.quiet=0):
    (∑s:Hot J,Poly.send s.val (L.part s.val))=L:=by
  ext q
  rw [Poly.part_sum]
  by_cases live:q.val.Nonempty
  · let v:Hot J:=⟨q,live⟩
    rw [Finset.sum_eq_single v]
    · simp [Poly.part_send,v]
    · intro s _ ne
      have miss:q≠s.val:=fun eq=>ne (Subtype.ext eq.symm)
      simp [Poly.part_send,miss]
    · simp
  · have eq:q=J.quiet:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp live)
    subst q
    rw [quiet]
    apply Finset.sum_eq_zero
    intro s _
    have miss:J.quiet≠s.val:=by
      intro h
      have hn:=s.property
      rw [←h] at hn
      exact Finset.not_nonempty_empty hn
    simp [Poly.part_send,miss]

theorem ordinary (L:Poly J)(quiet:L.part J.quiet=0):
    (∏s:Hot J,(1+Poly.send s.val (L.part s.val)))=Poly.pass L:=by
  exact (Extra.Trajectories.pass_sum univ (fun s:Hot J=>s.val) (fun s _=>s.property) _).symm.trans
    (congrArg Poly.pass (sum L quiet))

omit [Fintype V] in
theorem bare_quiet {G:Gauge}{n:Side}{I X:Type}{o:V→Site n}{b:BudgetPoint}
    (L:Lamps X I G b o J)(t:X)(U:Config G n):
    (WilsonRootedKioskOccupiedSlip.bare L t U).part J.quiet=0:=by
  unfold WilsonRootedKioskOccupiedSlip.bare
  by_cases full:Summable (fun i=>Poly.send (L.mode i) (L.nominal t i U))
  · rw [Poly.share full]
    simp only [Poly.part_send,if_neg (L.live _).symm,tsum_zero]
  · rw [tsum_eq_zero_of_not_summable full]
    rfl

end YM.Integration.WilsonOriginalConnectedSubmission
end
