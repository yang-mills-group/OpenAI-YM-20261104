import YM.Integration.WilsonOriginalRawForestRays
import YM.Comparison.RG02.Sources.Naming

/-! Restrict an actual finite nonbare history to its old name while retaining the whole
coupling board, original Gaussian and all held angles. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSingletonPin
open Filter Function Set Finset Wilson RG Precision Lattice Tree Exterior Marker Multi Source
open Comparison.RG02 Order AllOrder.Floe QuadraticLocal.Earn WilsonCoeffUV WilsonCoeffUV.Blue
open YM.Extra.Trajectories (Names)
open scoped Classical BigOperators Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V][Fintype V]
local notation "C" => Stock.census V
local notation "J" => Stock.census Unit
def seat (v:V):Names J (C) where
  e:=⟨fun _=>v,fun _ _ _=>Subsingleton.elim _ _⟩
  visible _:=mem_univ _
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(t:S.Choices)
  (v:V)(x:fieldDir G c 1)(r:ℕ)
theorem original (bank:Bulk.Colors (C) G f)(j:ℕ)(le:j≤r):
    (Order.observe (C) r (Order.logMarked (Bulk.Fk K F t bank x r)) j).part ((C).fire v)=
      (Order.observe J r (Order.logMarked (Bulk.Fk K F t (Sources.pin (seat v) bank) x r)) j).part ((J).fire ()):=by
  let u:=seat v
  let emb:=Function.Embedding.refl (Fin r)
  have leading:=Bulk.fk_unit K F t bank x r
  have narrow:=Order.trunc_observe u emb (Order.sym_logMarked leading (Bulk.fk_sym ..)) le
  rw [Sources.trunc_marked u emb leading,Sources.criterion] at narrow
  have h:=congrArg (fun q:Poly J=>q.part ((J).fire ())) narrow
  change (Order.observe (C) r (Order.logMarked (Bulk.Fk K F t bank x r)) j).part (u.share ((J).fire ()))=_ at h
  rw [u.fire] at h
  exact h

end YM.Integration.WilsonOriginalSingletonPin
