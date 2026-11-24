import YM.Integration.WilsonIndependentSpoutMasterClockFees

/-! The measured basis comparison includes the change of the two older reporting clocks. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterReportedBasis
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutMasterBasisCutoff (bank unit)
open WilsonIndependentSpoutMasterCutoff (rent Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h D k u e:ℕ}

theorem numeral (X:Ten ℝ (YForest G) 0){A:ℝ}(funded:Fruit 0 1 u X A):
    ‖X Fin.elim0‖ ≤ A:=by
  have slot:hedge 0 1 u (Fin.elim0:Fin 0→YForest G)*‖X Fin.elim0‖ ≤ A:=
    (funded.2.1.le_tsum _ (fun y _=>funded.1 y)).trans funded.2.2
  rw [autumn_empty G 1 0 u Fin.elim0] at slot
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul] using slot

theorem appeared {X Y:Era G ℝ}{A δ:ℝ}(paid:Fringed k e u 1 A δ X Y)(j:ℕ)(hj:j ≤ e):
    twain A δ (PowerSeries.coeff j (ground X)) (PowerSeries.coeff j (ground Y)):=by
  have pair:=paid.heapS j 0 hj
  simpa only [ground,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk] using
    (show twain A δ (X.2 j 0 Fin.elim0) (Y.2 j 0 Fin.elim0) from
      ⟨numeral _ pair.wax,numeral _ pair.wane,numeral _ pair.toll⟩)

theorem timed {X Y:Era G ℝ}{A:ℝ}(R:Run G)(v m K N' j:ℕ){C:Credit}(schedule:Paid R j e C)
    (wake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)(live:K ≤ N')
    (paid:Fringed k e u 1 A (trailC R.family.S m K) X Y)(q:ℕ)(hq:q ≤ e):
    let L:=R.family.path.levels
    twain (((q+1:ℕ):ℝ)*(2*C.buy (Compar L.S (zz L) v m)*A)) (trailC L.S m K)
      (PowerSeries.coeff q (report L R.metals.O N' m v (ground X)))
      (PowerSeries.coeff q (report L R.metals.O K m v (ground Y))):=by
  intro L
  unfold report
  simp only [reelQuote]
  have paid' s (hs:s∈range (q+1)):= (appeared paid s (by have:=Finset.mem_range.mp hs; omega)).mul
    (schedule v m K N' (q-s) s wake early pre live (by omega) (by have:=Finset.mem_range.mp hs; omega))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using twain.sum _ paid'

variable (R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels
def price (C wallet gates:Credit)(v m q:ℕ)(Z:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
    ((q+1:ℕ):ℝ)*(2*gates.buy (Compar (L₀).S (zz L₀) v m)*(C.buy Z*∏i,B i*wallet.buy (zz L₀ m)))

theorem original {j:ℕ}{C W budget:Credit}(sale:Earned R l d admit j e u C W)(fees:Paid R j e budget)
    (v m K N':ℕ)(a:∀i,Alma (Q₀ i).F)(F:Wilt Q₀)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)(top:K ≤ N')
    (optic:Compar (L₀).S (zz L₀) v m ≤ Z)(fit:Bough Q₀ F y Z B)(q:ℕ)(hq:q ≤ e):
    twain (price R C W budget v m q Z B) (trailC (L₀).S m K)
      (PowerSeries.coeff q (report L₀ R.metals.O N' m v (ground (stopped L₀ R.metals.O Q₀ F (bank Q₀ a) m K N' v y o))))
      (PowerSeries.coeff q (report L₀ R.metals.O K m v (ground (stopped L₀ R.metals.O Q₀ F (bank Q₀ a) m K K v y o)))):=by
  have forms:=(sale m K N' v (bank Q₀ a) F B Z y o awake early pre top optic fit).1
  simpa only [price,rent,WilsonIndependentSpoutMasterBasisCutoff.unit,mul_one] using timed R v m K N' j fees awake early pre top forms q hq
end YM.Integration.WilsonIndependentSpoutMasterReportedBasis
end
