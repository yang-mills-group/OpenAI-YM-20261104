import YM.Integration.WilsonIndependentSpoutMasterReportedBasis
import YM.Integration.WilsonIndependentSpoutMasterAppointments
import YM.Integration.WilsonIndependentFittedRosterCash
import YM.Integration.RunFormalChain

/-! The numerical normalized master transfer between the buffered and fresh openings. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterCash
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonIndependentSpoutMasterCutoff (Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentSpoutMasterAppointments (Grants)
open WilsonIndependentSpoutMasterReportedBasis (price)
open WilsonIndependentSpoutMasterBasisCutoff (bank)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentFittedRosterCash (numerical reserve roster)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e u:ℕ}
private theorem expanded (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (Q:Fin (n+1)→SealR G)(F:Wilt Q)(b:Herit Q)(m K χ v:ℕ)(y:ℝ)(o:CellR)
    (early:v ≤ m)(pre:m ≤ K)(birth:K ≤ χ)
    (offered:∀i a,Auth (Q i).h (WilsonIndependentSpoutMasterArms.arm A O (Q i) (F i) (axis (Q i) a) m K χ y o)):
    report A O χ m v (ground (stopped A O Q F b m K χ v y o))=
      roster (J:=fun i=>Alma (Q i).F) b (fun a=>report A O χ m v (ground (stopped A O Q F (bank Q a) m K χ v y o))):=by
  have checked:=WilsonIndependentSpoutMasterReport.original A O simple valid Q F b m K χ v y o early pre birth offered
  rw [checked]
  unfold roster
  apply Finset.sum_congr (by ext a; simp only [Finset.mem_univ])
  intro a _
  rfl

variable (R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels

def reading (F:Wilt Q₀)(b:Herit Q₀)(m K χ v:ℕ)(y:ℝ)(o:CellR):Cost:=
  report L₀ R.metals.O χ m v (ground (stopped L₀ R.metals.O Q₀ F b m K χ v y o))

theorem basis {j:ℕ}{C W D:Credit}(sale:Earned R l d admit j e u C W)(fees:Paid R j e D)
    (v m K N':ℕ)(a:∀i,Alma (Q₀ i).F)(F:Wilt Q₀)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)(top:K ≤ N')
    (optic:Compar (L₀).S (zz L₀) v m ≤ Z)(fit:Bough Q₀ F y Z B)(q:ℕ)(hq:q ≤ e):
    belt q (embed (reading R l d admit F (bank Q₀ a) m K N' v y o -
      reading R l d admit F (bank Q₀ a) m K K v y o)) ≤
    (∑i∈range (q+1),price R C W D v m i Z B)*trailC (L₀).S m K:=by
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have earned:=WilsonIndependentSpoutMasterReportedBasis.original R l d admit sale fees v m K N' a F B Z y o
    awake early pre top optic fit i (by have:=Finset.mem_range.mp hi; omega)
  have realNorm (t:ℝ):‖algebraMap ℝ ℂ t‖=‖t‖:=Complex.norm_real t
  simp only [reading,embed,PowerSeries.coeff_map,realNorm]
  rw [map_sub]
  exact earned.gap

theorem original (simple:G.Simple){j:ℕ}{C W D:Credit}(sale:Earned R l d admit j e u C W)
    (fees:Paid R j e D)(fields:Grants R l d admit j)
    (v m K N':ℕ)(b:Herit Q₀)(F:Wilt Q₀)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)(top:K ≤ N')
    (optic:Compar (L₀).S (zz L₀) v m ≤ Z)(fit:Bough Q₀ F y Z B)(q:ℕ)(hq:q ≤ e)
    (g:ℝ)(small:|g|≤1):
    ‖cash q g (embed (reading R l d admit F b m K N' v y o - reading R l d admit F b m K K v y o))‖ ≤
      (numerical q g b+((Fintype.card (Fin (n+1)):ℝ)+1)*|g|^(q+1)*reserve q b)*
      ((∑i∈range (q+1),price R C W D v m i Z B)*trailC (L₀).S m K):=by
  let row (χ:ℕ)(a:∀i,Alma (Q₀ i).F):=reading R l d admit F (bank Q₀ a) m K χ v y o
  have valid:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  have split (χ:ℕ)(birth:K ≤ χ):
      reading R l d admit F b m K χ v y o=roster (J:=fun i=>Alma (Q₀ i).F) b (row χ):=by
    have offered (i:Fin (n+1)) (a:Alma (Q₀ i).F):=fields i (F i) (axis (Q₀ i) a) m K χ y o (awake.trans (early.trans pre)) birth
    exact expanded L₀ R.metals.O simple valid Q₀ F b m K χ v y o early pre birth offered
  rw [split N' top,split K le_rfl]
  have difference:roster b (row N')-roster b (row K)=roster b (fun a=>row N' a-row K a):=by
    simp only [roster,mul_sub,Finset.sum_sub_distrib]
  rw [difference]
  exact WilsonIndependentFittedRosterCash.original q g small b _ _ (fun a=>
    basis R l d admit sale fees v m K N' a F B Z y o awake early pre top optic fit q hq)

end YM.Integration.WilsonIndependentSpoutMasterCash
end
