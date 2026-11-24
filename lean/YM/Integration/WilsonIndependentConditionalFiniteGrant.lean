import YM.Integration.WilsonIndependentConditionalRawSpout
import YM.Integration.WilsonIndependentConditionalCappedBlue
import YM.Integration.WilsonIndependentConditionalThermalCap

/-! This physical-age grant requires a rooted income only for the
retained marked coefficients and an intensive income only for the
positive angular coefficients of the action, up to the paid degree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalFiniteGrant
open Filter Matrix RG Lattice WilsonCoeffUV Blue Bank Soil RegulatorIR Budget Diagram
open Bloch Laurent Metric Precision FreeResolvent Work.F08 Wilson Tree
open AnalyticNext.QuarticMatch.Sheets Exterior WilsonCoeffUV.Mer Embroider
open WilsonIndependentConditionalUnshiftedQuiet WilsonIndependentConditionalUnshiftedExit
open WilsonIndependentConditionalRawSpout
open scoped Topology BigOperators Classical

def tip {I:Type}(V:Orders I)(d:ℕ):Orders I:=fun i r=>if i≤d∧0<r then V i r else 0
def ink {I:Type}(V:Orders I)(d:ℕ):Orders I:=fun i=>if i≤d then V i else 0

theorem original {G:Gauge}(A:Levels G){m N:ℕ}(finer:m<N)
    {V F:(n:Side)→ Pal ℝ (Co n (Hinge G (loose A m).L))}
    {P Z:Pal ℝ (Cloth (Hinge G (loose A m).L))}{d:ℕ}
    (quiet:∀i≤d,∀r,0<r→Yields (fun n=>V n i r) (P i r))
    (vp:∀n i,i≤d→Pure (V n i))
    (marked:∀i≤d,∀r,Bends 0 (fun n=>F n i r) (Z i r))(mp:∀n i,i≤d→Pure (F n i))
    (k e r:ℕ)(he:e≤d):
    let B:=loose A m;let K:=A.clock.kernel;let H:=freeForms A N (m+1);let Γ:=kernel B (shuttleM (conditional A N m))
    let M:=post B (shuttleM (feedA A N m))
    Bends 0 (fun n=>scoop (fade (ends B K (roam A N m) n) (finite (matrix B K H n) (V n) (F n) k e) r))
      (scoop (Packet.draft M.transpose (endHeat k Γ (logHeat Γ P false) Z e r))):=by
  intro B K H Γ M
  have q (i s):Yields (fun n=>tip (V n) d i s) (tip P d i s):=by
    by_cases h:i≤d∧0<s
    · simpa only [tip,if_pos h] using quiet i h.1 s h.2
    simp only [tip,if_neg h];exact Yields.zero
  have v (n i):Pure (tip (V n) d i):=by
    intro s
    by_cases h:i≤d∧0<s
    · simpa only [tip,if_pos h] using vp n i h.1 s
    simp only [tip,if_neg h];exact Smooth.zero
  have a (i s):Bends 0 (fun n=>ink (F n) d i s) (ink Z d i s):=by
    by_cases h:i≤d
    · simpa only [ink,if_pos h] using marked i h s
    simp only [ink,if_neg h];exact Bends.zero
  have f (n i):Pure (ink (F n) d i):=by
    by_cases h:i≤d
    · simpa only [ink,if_pos h] using mp n i h
    intro s;simp only [ink,if_neg h];exact Smooth.zero
  have income:=WilsonIndependentConditionalRawSpout.original A finer q v a f k e r
  have cover:=WilsonIndependentConditionalThermalCap.original Γ (d:=d) (V:=tip P d) (W:=P)
    (F:=ink Z d) (G:=Z) (fun i hi s hs=>if_pos ⟨hi,hs⟩) (fun i hi=>if_pos hi) k he
  have bank (n:Side):finite (matrix B K H n) (tip (V n) d) (ink (F n) d) k e=
      finite (matrix B K H n) (V n) (F n) k e:=by
    apply Finset.sum_congr rfl;intro j _
    exact WilsonIndependentConditionalCappedBlue.marked (matrix B K H n) (d:=d)
      (fun i hi s hs=>if_pos ⟨hi,hs⟩) (fun i hi=>if_pos hi) j e he
  dsimp only at income
  rw [show endHeat k Γ (logHeat Γ P false) Z e r=endHeat k Γ (logHeat Γ (tip P d) false) (ink Z d) e r from (congrFun cover r).symm]
  exact income.congr (Eventually.of_forall fun n=>by rw [bank n])

end YM.Integration.WilsonIndependentConditionalFiniteGrant
