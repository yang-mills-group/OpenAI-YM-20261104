import YM.Integration.WilsonIndependentSpoutMasterUpperClocks
import YM.Integration.WilsonIndependentSpoutMasterReportedBasis
import YM.Integration.WilsonIndependentFittedMixedCash

/-! Changing the reporting clock on the buffered normalized field, at an independently chosen UV depth. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterBufferedClock
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonIndependentSpoutMasterUpperClocks (Paid)
open WilsonIndependentSpoutMasterCutoff (Earned rent)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e u:ℕ}(R:Run G)
local notation "L₀" => R.family.path.levels

theorem timed {j:ℕ}{C:Credit}(income:Paid R j e C)(v m U N M:ℕ)(wake:j ≤ v)(vm:v ≤ m)
    (step:m ≤ U)(live:U ≤ N)(twin:U ≤ M)(F:Cost)(A:ℝ)(salary:∀t ≤ e,‖PowerSeries.coeff t F‖ ≤ A)
    (q:ℕ)(depth:q ≤ e):
    twain (((q+1:ℕ):ℝ)*(2*C.buy (Compar (L₀).S (zz L₀) v m)*A)) (trailC (L₀).S m U)
      (PowerSeries.coeff q (report L₀ R.metals.O N m v F)) (PowerSeries.coeff q (report L₀ R.metals.O M m v F)):=by
  unfold report
  simp only [reelQuote]
  have terms s (hs:s∈range (q+1)):= (twain.one (PowerSeries.coeff s F) A (trail_pos (L₀).S m U).le
    (salary s (by have:=Finset.mem_range.mp hs; omega))).mul
    (income v m U N M (q-s) s wake vm step live twin (by omega) (by have:=Finset.mem_range.mp hs; omega))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using twain.sum _ terms

variable (l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit

theorem original {j:ℕ}{C W D:Credit}(sale:Earned R l d admit j e u C W)(income:Paid R j e D)
    (v m K U N M:ℕ)(b:Herit Q₀)(F:Wilt Q₀)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)(buffer:K ≤ U)(live:U ≤ N)(twin:U ≤ M)
    (optic:Compar (L₀).S (zz L₀) v m ≤ Z)(fit:Bough Q₀ F y Z B)(q:ℕ)(hq:q ≤ e)(g:ℝ)(small:|g|≤1):
    let Y:=ground (stopped L₀ R.metals.O Q₀ F b m K M v y o)
    let A:=rent C W (zz L₀) Q₀ b e m Z B
    ‖cash q g (embed (report L₀ R.metals.O N m v Y - report L₀ R.metals.O M m v Y))‖ ≤
      (∑s∈range (q+1),((s+1:ℕ):ℝ)*(2*D.buy (Compar (L₀).S (zz L₀) v m)*A))*trailC (L₀).S m U:=by
  intro Y A
  have forms:=(sale m K M v b F B Z y o awake early pre (buffer.trans twin) optic fit).1
  have wages s (hs:s ≤ e):‖PowerSeries.coeff s Y‖ ≤ A:=(WilsonIndependentSpoutMasterReportedBasis.appeared forms s hs).main
  apply (WilsonIndependentFittedMixedCash.cash_le q g small _).trans
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs=>?_
  have row:=timed R income v m U N M awake early (pre.trans buffer) live twin Y A wages s (by have:=Finset.mem_range.mp hs; omega)
  have realNorm (t:ℝ):‖algebraMap ℝ ℂ t‖=‖t‖:=Complex.norm_real t
  simp only [embed,PowerSeries.coeff_map,realNorm]
  rw [map_sub]
  exact row.gap
end YM.Integration.WilsonIndependentSpoutMasterBufferedClock
end
