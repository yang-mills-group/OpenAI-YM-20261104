import YM.Integration.WilsonRootedKioskWithdrawal

/-! Sum every actually paid filed occurrence before the second tap. The
finite period is used only for summability. The rooted charge is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskCompleteFiling
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal RG3
open WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I J E:Type}[DecidableEq V]
  {o:V → Site n}{R:Census V}{p:BudgetPoint}{a g:ℝ}{B:ℕ}{w:V → ℝ}
variable (L:Lamps T I G p o R)(hw:∀v,0<w v)(ha:0 ≤ a)(native:Gross L w B a g)

include hw ha native

theorem sums (t:T)(u:Config G n):
    Summable (fun i=>Poly.send (L.mode i) (L.nominal t i u)) ∧ Summable (fun i=>(sheet L).soap t i u):=by
  obtain ⟨f,pos,all,hit⟩:=native.before
  have summable:Summable (fun i=>Poly.toll w (L.mode i)*f i):=
    (Letters.Frame.from_hit B a g _ (fun i=>⟨(L.address i).site,(L.address i).anchor⟩)
      (fun i=>mul_nonneg (Poly.worth hw _).le (pos i)) ha hit).2.1
  constructor
  · apply (Poly.budgeted hw summable ?_).1;intro i
    rw [Poly.solo];exact mul_le_mul_of_nonneg_left (all i t u) (Poly.worth hw _).le
  · apply (Poly.budgeted hw summable ?_).1;intro i
    change Poly.price w (Poly.send (L.mode i) (gap L t i u)) ≤ _
    rw [Poly.solo];exact mul_le_mul_of_nonneg_left ((size L t i u).trans (all i t u)) (Poly.worth hw _).le

theorem split (t:T)(u:Config G n): L.log t u=bare L t u+(sheet L).log t u:=by
  obtain ⟨full,slip⟩:=sums L hw ha native t u
  unfold WilsonRootedKioskOccupiedSlip.bare Canopy.ShiftRows.log Lamps.log
  rw [←full.tsum_add slip]
  apply tsum_congr;intro i
  change Poly.send _ (L.light t i u)=Poly.send _ (L.nominal t i u)+Poly.send _ (gap L t i u)
  rw [←Extra.Trajectories.send_add,gap];congr 1;abel

theorem quiet (t:T)(u:Config G n):(bare L t u).part R.quiet=0:=by
  unfold WilsonRootedKioskOccupiedSlip.bare
  rw [Poly.share (sums L hw ha native t u).1]
  simp [Poly.part_send,fun i=>(L.live i).symm]

end YM.Integration.WilsonRootedKioskCompleteFiling
