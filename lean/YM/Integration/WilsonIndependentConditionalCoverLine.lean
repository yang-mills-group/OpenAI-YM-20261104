import YM.Integration.WilsonIndependentConditionalMarkedCover
import YM.RegulatorIR.Diagram.Heat

/-! The unsummed retained marked contraction on the genuine infinite cover.
The two wires in the ordinary rooted sum are the same two covariance ends. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverLine
open RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank
open Lattice Laurent Bloch Matrix RegulatorIR RegulatorIR.Diagram RegulatorIR.Budget
open RegulatorIR.Budget.Packet
open scoped Classical BigOperators

variable {α:Type}
private theorem symmetric {I:Type}{r:ℕ}{T:Packet I (r+2)}(h:Smooth T)(K:Layer I I):
    Packet.IsSym (loop T K):=by
  intro π x
  apply tsum_congr;intro y
  change K y.1 y.2 * prune (prune T y.1) y.2 (x∘π)=K y.1 y.2 * prune (prune T y.1) y.2 x
  rw [((h.prune y.1).prune y.2) π x]

theorem original (K:ropes Cover α α)(sym:∀ x y,K x y=K y x)(T:Gen ℝ (Cloth α))
    (r:ℕ)(pure:Smooth (T (r+2))):rime K T r=heating K T r:=by
  funext x
  rw [heating, Packet.symmetric_already _ (symmetric pure K)]
  change (∑' y,rain K T r x y)=((r+2:ℝ)*(r+1:ℝ)/2)*(∑' y,curve (T (r+2)) K x y)
  rw [←tsum_mul_left,←((finTwoArrowEquiv (Cloth α)).trans (Equiv.prodComm _ _)).tsum_eq]
  apply tsum_congr;intro y
  rw [rain_spell]
  change _=_*(K (y 1) (y 0)*T (r+2) (Fin.cons (y 1) (Fin.cons (y 0) x)))
  rw [smul_eq_mul,sym (y 1) (y 0)]
  push_cast
  ring

theorem period [Fintype α] {p:Cover}{r:ℕ}{K:ropes Cover α α}
    {G:(n:Side) → ropes (Site n) α α}{T:Gen ℝ (Cloth α)}{V:(n:Side)→Gen ℝ (Co n α)}
    (fund:Pilots G K)(sky:∀ x y,K x y=K y x)(mark:Bends p (fun n=>V n (r+2)) (T (r+2)))
    (pure:Smooth (T (r+2))):Bends p (fun n=>ripple (G n) (V n) r) (heating K T r):=by
  rw [←original K sky T r pure]
  exact rime_period fund mark

end YM.Integration.WilsonIndependentConditionalCoverLine
