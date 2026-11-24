import YM.Integration.WilsonIndependentSpoutMasterCoordinates

/-! Finite profiles and the complete deposited master preserve the scalar weights on each original arm. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterWords
open Lattice Wilson RG Source Labels XSpace Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Mer WilsonCoeffUV.Power
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningPayment (affiled carried)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentSpoutMasterCoordinates (axis)
open scoped Classical BigOperators
variable {G:Gauge}{h D:ℕ}{J:Type}[Fintype J]

def view (b:Volume D)(z:Cover)(P:TowerS G D):Era G ℝ:=
  shifted (tuftV (ContinuousLinearMap.apply ℝ ℝ b) P) z

theorem census (b:Volume D)(z:Cover)(P:J→TowerS G D):
    view b z (∑j,P j)=∑j,view b z (P j):=by
  refine Prod.ext (funext fun n=>?_) ?_
  · funext e r v
    change jot b ((∑j,P j).1 n) e r _=_
    simp only [Prod.fst_sum,Finset.sum_apply,map_sum]
    rfl
  funext e r v
  change jot b ((∑j,P j).2) e r _=_
  simp only [Prod.snd_sum,Finset.sum_apply,map_sum]
  rfl

theorem letter (b:Volume D)(z:Cover)(P:TowerS G D)(c:Cost):
    view b z (Stem c P)=affiled c (view b z P):=
  Prod.ext (funext fun n=>carried (wrap n z) b c (P.1 n)) (carried z b c P.2)

omit [Fintype J] in
theorem ledger (P:J→Era G ℝ)(c:Cost)(s:Finset J)(u:ℝ):
    affiled c (∑j∈s,u • P j)=∑j∈s,u • affiled c (P j):=by
  refine Prod.ext (funext fun n=>?_) ?_
  · change affix c ((∑j∈s,u • P j).1 n)=_
    simp only [Prod.fst_sum,Finset.sum_apply,Prod.smul_fst,Pi.smul_apply,affix_sum,affix_μ]
    rfl
  change affix c ((∑j∈s,u • P j).2)=_
  simp only [Prod.snd_sum,Prod.smul_snd,affix_sum,affix_μ]
  rfl

theorem profile (c:J → Cost)(P:J→TowerS G D)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x):
    word (∑j,Stem (c j) (P j)) φ x y o l=∑j,affiled (c j) (word (P j) φ x y o l):=by
  simp only [word,pupil_eye l _ φ x y o hx]
  change (∑z∈VisitsT φ x y o,drumB l x • view (wheelC x y z φ.ψ o) z (∑j,Stem (c j) (P j)))=
    ∑j,affiled (c j) (∑z∈VisitsT φ x y o,drumB l x • view (wheelC x y z φ.ψ o) z (P j))
  simp_rw [census,letter,Finset.smul_sum,ledger]
  rw [Finset.sum_comm]

theorem shrine {F:Frame G h}(B:Island F D)(c:J → Cost)(P:J→Verse F):
    Shrine B (fun a=>∑j,c j*P j a)=∑j,Stem (c j) (Shrine B (P j)):=by
  refine Prod.ext (funext fun n=>?_) ?_
  · simp only [Shrine,Stem,Prod.fst_sum,Finset.sum_apply,affix_sum,affix_mul,addend]
    rw [Finset.sum_comm]
  simp only [Shrine,Stem,Prod.snd_sum,affix_sum,affix_mul,addend]
  rw [Finset.sum_comm]

end YM.Integration.WilsonIndependentSpoutMasterWords
end
