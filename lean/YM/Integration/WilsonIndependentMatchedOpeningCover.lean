import YM.Integration.WilsonIndependentMatchedOpeningBoard
import YM.Integration.WilsonIndependentMatchedOpeningStalk
import YM.Integration.WilsonIndependentNotebookPayrollMark
/-! Recover the whole cover opening on the original clock, including thermal and angular rank zero. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningCover
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Rose Gauge
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open PertExtension RegulatorIR RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Prim RegulatorIR.Diagram RegulatorIR.Halo RegulatorIR.Oracle RegulatorIR.Cluster
open RegulatorIR.Diagram RegulatorIR.Ward RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Calibration
open WilsonIndependentConditionalNativeLinks (coarse)
open WilsonIndependentConditionalCoordinateHeat (orders)
open WilsonIndependentSpoutAtomicPolar (seats)
open WilsonIndependentSpoutFiniteStencil (coordinates)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open WilsonIndependentMatchedOpeningBoard (folded)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOrdinarySeat (here)
open scoped Classical Topology
variable {G:Gauge}
theorem recover {h:ℕ}(T:Orders (Foot G))(M:Era G ℝ)(auth:Auth h M)
    (finite:∀e r,Bounded (T e r))(symmetric:gradedSymmetric T)(scope:Ranks h T)
    (ray:∀(n:Side)(v:TreeVars G n),here n v (Blue.flash (M.1 n))=RegulatorIR.Halo.shelter h T (sample v)):
    T=orders (coarse G) M.2:=by
  funext e r q
  have cov:= (auth.wing e r).point (coarse G∘q)
  have fin:=WilsonIndependentMatchedOpeningStalk.original (T e r) (finite e r) q
  have eqn (n:Side):M.1 n e r (foldUnder n∘(coarse G∘q))=folded n (T e) r (coordinates n∘q):=by
    have ht:=congrFun (congrFun (WilsonIndependentMatchedOpeningBoard.recover T M auth finite
      symmetric scope n (ray n) e) r) (coordinates n∘q)
    exact ht.symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (fin.mono (fun _ h=>h.symm)))
    (cov.congr eqn)

private theorem unmixed (Q:Pal ℝ (YForest G)):Blue.mix 1 Q=Q:=by
  funext e r
  unfold Blue.mix
  rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_self e))]
  · simp
  · intro i hi ne
    have z:e-i≠0:=by have:=Finset.mem_range.mp hi;omega
    simp [PowerSeries.coeff_one,z]

theorem source (T:Orders (Foot G))(M:Era G ℝ)(link:T=orders (coarse G) M.2)
    {I:Type}{J:I→ℕ}(A:I→Levels G)(s:I→ℕ)(i:I):
    T=WilsonIndependentNotebookPayrollMark.source A s (Page.opening J i) M:=by
  change T=orders (coarse G) (Blue.mix 1 M.2)
  rwa [unmixed]
end YM.Integration.WilsonIndependentMatchedOpeningCover
