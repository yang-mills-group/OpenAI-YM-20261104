import YM.Integration.WilsonIndependentConditionalHeldDraft
import YM.Integration.WilsonIndependentConditionalRawVacuum

/-! The held vacuum file with the same per-slot predictor as the native finite decoder. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalPureReceiver
open Function Matrix Filter Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open Bloch Laurent Metric Precision FreeResolvent Work.F08 Wilson Tree
open AnalyticNext.QuarticMatch.Sheets Exterior WilsonCoeffUV.Mer Embroider
open WilsonCoeffUV.Soil RegulatorIR RegulatorIR.Diagram RegulatorIR.Budget.Packet
open WilsonIndependentConditionalUnshiftedQuiet WilsonIndependentConditionalUnshiftedExit
open WilsonIndependentConditionalRawVacuum (finite)
open scoped Topology BigOperators Classical
theorem original {G:Gauge}(A:Levels G){m N d:ℕ}(finer:m<N)
    {V:(n:Side)→Pal ℝ (Co n (Hinge G (loose A m).L))}{T:Pal ℝ (Cloth (Hinge G (loose A m).L))}
    (quiet:∀ i≤d,∀ r,0<r→Yields (fun n=>V n i r) (T i r))(pure:∀n i,Pure (V n i))
    (e r:ℕ)(he:e≤d)(hr:0<r):
    let B:=loose A m;let K:=A.clock.kernel;let H:=freeForms A N (m+1);let Γ:=kernel B (shuttleM (conditional A N m))
    let M:=post B (shuttleM (feedA A N m))
    Yields (fun n=>scoop (fade (ends B K (roam A N m) n) (finite (matrix B K H n) (V n) e) r))
      (scoop (draft M.transpose (ceaseHeat Γ T false e r))):=by
  intro B K H Γ M
  let g:=resin A N m finer
  have inc:=WilsonIndependentConditionalUnshiftedQuiet.covariance B K g
  have sym:=WilsonIndependentConditionalUnshiftedQuiet.symmetric B K g (fun n=>Bank.age_sym A N (m+1) (n*B.L))
  have money:=WilsonIndependentConditionalRawVacuum.covered inc sym quiet (fun n i _=>pure n i) e r he hr
  have shape:=money.sym (Eventually.of_forall fun n=>(pure_sum fun j _=>pure_abr _ (pure n) j e) r)
  rw [WilsonIndependentConditionalHeldDraft.original (capit (predictor B K g)) money shape,transpose_transpose]
  exact WilsonIndependentConditionalRawVacuum.original A finer quiet (fun n i _=>pure n i) e r he hr

end YM.Integration.WilsonIndependentConditionalPureReceiver
