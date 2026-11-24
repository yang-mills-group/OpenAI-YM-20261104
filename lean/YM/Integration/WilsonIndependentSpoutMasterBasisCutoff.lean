import YM.Integration.WilsonIndependentSpoutMasterCoordinates
import YM.Integration.WilsonIndependentSpoutMasterCutoff
import YM.Integration.WilsonIndependentMatchedPhysicalPeer

/-! Transfer on each normalized master pivot, with its exact before-cutoff price. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterBasisCutoff
open Filter Lattice Wilson RG Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider Source Labels
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentSpoutMasterCutoff (Earned rent)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e u:ℕ}(Q:Fin (n+1)→SealR G)

def bank (a:∀i,Alma (Q i).F):Herit Q:=fun i=>axis (Q i) (a i)

def measured (b:Herit Q)(φ:Fin (n+1)→PowerSeries ℝ→ₗ[ℝ]ℝ):Herit Q:=
  fun i j=>PowerSeries.C ((φ i) (b i j))

theorem constant (x:ℝ)(e:ℕ):
    ∑j:Fin (e+1),‖PowerSeries.coeff j.val (PowerSeries.C x)‖=‖x‖:=by
  rw [Finset.sum_eq_single (0:Fin (e+1))]
  · simp
  · intro j _ other
    have pos:j.val ≠ 0:=fun h=>other (Fin.ext h)
    rw [PowerSeries.coeff_C,if_neg pos,norm_zero]
  · simp

theorem marked (b:Herit Q)(φ:Fin (n+1)→PowerSeries ℝ→ₗ[ℝ]ℝ)(e:ℕ)(i:Fin (n+1)):
    fee (measured Q b φ) e i=WilsonIndependentMatchedPhysicalPeer.amount (Q:=Q i) (φ i) (b i):=by
  simp only [fee,measured,constant,WilsonIndependentMatchedPhysicalPeer.amount]

theorem unit (a:∀i,Alma (Q i).F)(e:ℕ)(i:Fin (n+1)):
    fee (bank Q a) e i=1:=by
  classical
  unfold fee
  rw [Finset.sum_eq_single (a i)]
  · simpa only [bank,WilsonIndependentSpoutMasterCoordinates.axis,ite_true,map_one,norm_one] using constant 1 e
  · intro b _ ne
    simp [bank,WilsonIndependentSpoutMasterCoordinates.axis,ne]
  · simp

variable (R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels

theorem original {j:ℕ}{C wallet:Credit}(sale:Earned R l d admit j e u C wallet)
    (m K N' host:ℕ)(a:∀i,Alma (Q₀ i).F)(F:Wilt Q₀)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ host)(early:host ≤ m)(pre:m ≤ K)(top:K ≤ N')
    (optic:Compar (L₀).S (zz L₀) host m ≤ Z)(fit:Bough Q₀ F y Z B)(q:ℕ)(hq:q ≤ e):
    ‖PowerSeries.coeff q (ground (stopped L₀ R.metals.O Q₀ F (bank Q₀ a) m K N' host y o))-
       PowerSeries.coeff q (ground (stopped L₀ R.metals.O Q₀ F (bank Q₀ a) m K K host y o))‖ ≤
      (C.buy Z* ∏i,B i*wallet.buy (zz L₀ m))*trailC (L₀).S m K:=by
  simpa only [rent,unit,mul_one] using (sale m K N' host (bank Q₀ a) F B Z y o awake early pre top optic fit).2 q hq
end YM.Integration.WilsonIndependentSpoutMasterBasisCutoff
end
