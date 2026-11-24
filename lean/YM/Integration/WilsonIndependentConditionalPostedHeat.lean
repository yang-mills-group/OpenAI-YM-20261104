import YM.Integration.WilsonIndependentConditionalQuietBank
import YM.Integration.WilsonIndependentSubmittedCoverVerse

/-! The chosen higher history and all its genuine positive vacuum ranks,
on the same cover as the complete submitted response. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalPostedHeat
open RegulatorIR.Budget RG WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard FreeResolvent Exterior Work.F08 Matrix Metric
open RegulatorIR RegulatorIR.Diagram WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer Precision Embroider Embroider.Canvas WilsonCoeffUV.Blue
open Lattice Laurent Bloch WilsonIndependentConditionalScalarConvention
open scoped Classical BigOperators
variable {G:Gauge}

theorem conduct {I:Type}(K:Layer I I){V U:ℕ→Orders I}(h:∀i,Positive (V i) (U i))
    (F:Orders I)(m:ℕ):endHeat m K V F=endHeat m K U F:=by
  have same (k:ℕ):markHeat K V F k=markHeat K U F k:=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
      cases k with
      | zero=>rw [markHeat_first,markHeat_first]
      | succ k=>
        funext e r
        rw [markHeat_next,markHeat_next,ih k (by omega)]
        have join:Diagram.drift K (markHeat K V F) V k=Diagram.drift K (markHeat K U F) U k:=by
          funext j s
          unfold Diagram.drift;apply Finset.sum_congr rfl;intro v hv
          have eq:v.1+v.2=k:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
          unfold Diagram.carry;apply Finset.sum_congr rfl;intro a _
          unfold Diagram.force;apply Finset.sum_congr rfl;intro t _
          simp only [matchTwo,ih v.1 (by omega),h v.2 a.2 (t.2+1) (by omega)]
        rw [join]
  change heated _ (markHeat K V F)=heated _ (markHeat K U F)
  rw [funext same]

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N:ℕ}(finer:m<N)(k:ℕ)(Z:Era G ℝ)(source:Auth k Z):
    let P:=loose A m;let K:=A.clock.kernel;let Γ:=shuttleM (conditional A N m)
    let M:=shuttleM (feedA A N m);let W:=actionW A Ñ N (m+1)
    let C:=stair (upper (β:=Hooks G) Γ 0) 0
    (verseI A Ñ m N k Z).2=Blue.mix (ratioHigh A Ñ N m)
      (fun e=>sluice (endHeat k C (logHeat C (stellar P K Ñ M W) false) (slidesJ P M Z.2) e)):=by
  intro P K Γ M W C
  rw [WilsonIndependentSubmittedCoverVerse.original A simple ratio finer Z source]
  apply congrArg (Blue.mix _)
  funext e;apply congrArg sluice
  exact congrFun (conduct C (WilsonIndependentConditionalQuietBank.original A simple ratio finer) _ k) e

end YM.Integration.WilsonIndependentConditionalPostedHeat
