import YM.Integration.WilsonIndependentSpoutInitialState
import YM.Integration.WilsonIndependentSpoutClockedPrint

/-! The complete bare page in the elected interaction convention, including thermal and angular zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPayrollSeeds
open Function Filter Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Power WilsonCoeffUV.Bank WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Diagram.Formal RegulatorIR.Oracle RegulatorIR.Clocks RegulatorIR.Ledger
open RegulatorIR.Binding RegulatorIR.Ward
open PertExtension Tree FreeResolvent Metric Precision Exterior RegulatorIR.Geometry.Field
open WilsonIndependentSpoutReportedQuiet (port cover)
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem thermal (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost):
    port A Ñ N m α 0=0:=by ext r q;rfl

theorem scalar (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)
    (N m:ℕ)(age:m≤N)(α:Cost)(e:ℕ):port A Ñ N m α e 0=0:=by
  have raw (j:ℕ)(n:Side):(story A Ñ N m).1 n j 0=0:=by
    have h:=congr_fun (congr_fun ((old A Ñ simple ratio N m age).basis n).clear j) 0
    exact h.symm
  have upper (j:ℕ):(story A Ñ N m).2 j 0=0:=by
    have h: Yields (fun n=>(story A Ñ N m).1 n j 0) ((story A Ñ N m).2 j 0):=
      (old A Ñ simple ratio N m age).patch j 0
    have zero:Yields (fun n=>(story A Ñ N m).1 n j 0) 0:=by
      simp only [raw];exact Yields.zero
    exact h.unique zero
  ext1 q
  simp [port,cover,Blue.mix,upper]

theorem clock (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ){α β:Cost}{p:ℕ}
    (paid:Squares p α β)(one:constantCoeff β=1):Matches p (port A Ñ N m α) (port A Ñ N m β):=by
  intro e he
  ext r q
  simp only [port,cover,WilsonIndependentSpoutClockedPrint.source paid one _ he]

theorem initial {W:Type}{M:W→ℕ}{sides:Page M→Side}(C:Circuit M sides)
    (t:Page M→Scale)(w:W)(bare:t (Page.opening M w)=Clocks.flat)
    (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N p:ℕ):
    Matches p (Circuit.padV G t w) (port A Ñ N N 1):=by
  intro e _
  by_cases zero:e=0
  · subst e;exact (vacuum_lo _ (C.fitsV G t w)).trans (thermal ..).symm
  ext1 r
  by_cases empty:r=0
  · subst r
    rw [scalar A Ñ simple ratio N N le_rfl 1 e]
    ext1 q
    simp [Circuit.padV,many,massive,WilsonIndependentSpoutMuralWindow.scalar]
  ext1 q
  exact WilsonIndependentSpoutInitialState.original t w bare A Ñ simple ratio N e r
    (Nat.pos_of_ne_zero zero) (Nat.pos_of_ne_zero empty) q

end YM.Integration.WilsonIndependentSpoutPayrollSeeds
