import YM.Integration.WilsonIndependentConditionalCoverDrift
import YM.RegulatorIR.Diagram.Valence

/-! Identification of every normalized bulk marked heat layer on its true
period family. Vacuum and marked fields keep their own source conditions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverHeat
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Lattice Laurent Bloch Matrix
open scoped Classical BigOperators
variable {α:Type}[Fintype α]{p:Cover}
variable {K:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}
variable {V:Layers ℝ (Cloth α)}{Y:(n:Side)→ Layers ℝ (Co n α)}
variable {P:Pal ℝ (Cloth α)}{F:(n:Side)→ Pal ℝ (Co n α)}

theorem original (fund:Pilots G K)(symmetric:K.transpose=K)
    (vac:∀i j r,Yields (fun n=>Y n i j r) (V i j r))
    (marked:∀i r,Bends p (fun n=>F n i r) (P i r))(shape:gradedSymmetric P)(k:ℕ):
    heap K V P k=markHeat K V P k:=by
  have charges := heap_period fund vac marked
  induction k using Nat.strong_induction_on with
  | h k ih=>
    cases k with
    | zero=>
      funext e r;rw [level,markHeat_first]
    | succ k=>
      funext e r
      rw [markHeat_next,inchC]
      simp only [Pi.smul_apply,Pi.add_apply,Nat.cast_succ]
      congr 1
      let Z:=heap K V P
      have coal:Smooth (Z k e (r+2)):=by rw [show Z k=markHeat K V P k from ih k (by omega)];exact markedSym K V shape k e (r+2)
      have same (x y):K x y=K y x:=congrFun (congrFun symmetric.symm x) y
      rw [add_assoc,WilsonIndependentConditionalCoverDrift.original fund symmetric
        (fun i _ j _ t=>vac i j t) (fun i _ j _ t=>charges i j t) r,
        WilsonIndependentConditionalCoverLine.original K same (Z k e) r coal]
      congr 1
      · rw [show Z k=markHeat K V P k from ih k (by omega)]
      · exact congrFun (congrFun (forcing_earlier (K:=K) k Z (markHeat K V P) V V (fun i hi=>ih i (by omega)) (fun _ _=>rfl)) e) r

theorem period (fund:Pilots G K)(symmetric:K.transpose=K)
    (vac:∀i j r,Yields (fun n=>Y n i j r) (V i j r))
    (marked:∀i r,Bends p (fun n=>F n i r) (P i r))(shape:gradedSymmetric P)(k e r:ℕ):
    Bends p (fun n=>bul (G n) (Y n) (F n) k e r) (markHeat K V P k e r):=by
  rw [←original fund symmetric vac marked shape]
  exact heap_period fund vac marked k e r

end YM.Integration.WilsonIndependentConditionalCoverHeat
