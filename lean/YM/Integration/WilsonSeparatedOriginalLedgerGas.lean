import YM.Integration.WilsonSeparatedOriginalCloseLedger
import YM.FormalOPE.RG10.MarkerLog

/-! The matched old-gas residual on every original configuration. Both tables
carry exactly the same physical vacuum density and all marked singleton rows. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalLedgerGas
open Function Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extra.Histories Push Local
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Records RG05Readout.Address
open Extra.Trajectories WilsonAllDateHarvestStability PhysicalNext.Repeat
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
variable {P:Rep G n}{rows:V→Three G n}{L Y:Config G n → Poly J}{o:V→Site n}{w:V→ℝ}{α:ℝ}

/-- The whole original unmarked gas, every old forced singleton row and the
selected mixed hard sheet are present on the same subset of flags. -/
def marked (P:Rep G n)(rows:V→Three G n)(K:Box n → Config G n → Poly J)(W:Config G n)(p:Box n):Poly J:=
  bar P.activities J W p+Mach J (fun i=>profile P.activities (rows i).2.2 p W)+K p W

def old (P:Rep G n)(rows:V→Three G n)(K:Box n → Config G n → Poly J)(W:Config G n):Poly J:=
  (((P.eval W:ℂ)⁻¹)*(Real.exp (P.exponent W):ℂ)) • field (marked P rows K W) (flags P.p.threshold W)

private def exponent (_P:Rep G n)(rows:V→Three G n)(H:Support n → Config G n → Poly J)(W:Config G n):Poly J:=
  Mach J (fun v=>(rows v).2.1 W)+∑ X,H X W

private theorem quiet (D:Ledger P rows L o w α)(W:Config G n):
    (exponent P rows D.H W).part J.quiet=0:=by
  unfold exponent;rw [Poly.part_plus,mute,Poly.part_sum];simp only [(D.legal.exp _).1.sil];simp

private theorem density (D:Ledger P rows L o w α)(W:Config G n):
    (P.eval W:ℂ)⁻¹ • L W=Poly.pass (exponent P rows D.H W)*old P rows D.K W:=by
  rw [congrFun D.paid W];unfold restore exponent old marked
  rw [smul_smul,Algebra.mul_smul_comm]

/-- Even on a rough field the scalar part of the old normalized gas is
identical in the two ledgers, since each of their witnessed hard edits starts
at two occupied names. -/
theorem vacuum (B:Ledger P rows L o w α)(Z:Ledger P rows Y o w α)(W:Config G n):
    (old P rows Z.K W).part J.quiet=(old P rows B.K W).part J.quiet:=by
  have passive {A:Config G n → Poly J}(D:Ledger P rows A o w α)(p:Box n):(D.K p W).part J.quiet=0:=by
    by_contra awake
    have large:=(D.legal.flag p).2 W J.quiet awake
    change 2≤(∅:Finset V).card at large
    simp at large
  have site (p:Box n):(marked P rows Z.K W p).part J.quiet=(marked P rows B.K W p).part J.quiet:=by
    simp only [marked,Poly.part_plus,passive Z p,passive B p]
  have product (t:Finset (Box n)):(∏p∈t,marked P rows Z.K W p).part J.quiet=(∏p∈t,marked P rows B.K W p).part J.quiet:=by
    induction t using Finset.induction_on with
    | empty=>rfl
    | insert a s fresh ih=>rw [prod_insert fresh,prod_insert fresh,Poly.quiet_mul,Poly.quiet_mul,ih,site]
  unfold old;rw [Poly.part_smul,Poly.part_smul];congr 1
  unfold field;rw [Poly.part_sum,Poly.part_sum];apply Finset.sum_congr rfl;intro X _
  unfold grid;split
  · exact product X
  · rfl

/-- The original joint density before taking its connected coefficient,
including both old gases evaluated at the very same field. -/
theorem difference (B:Ledger P rows L o w α)(Z:Ledger P rows Y o w α)(W:Config G n)
    (whole:(((P.eval W:ℂ)⁻¹ • Y W):Poly J).part J.quiet=1):
    connected ((P.eval W:ℂ)⁻¹ • Y W)-connected ((P.eval W:ℂ)⁻¹ • L W)=
      (∑X,(Z.H X W-B.H X W))+(connected (old P rows Z.K W)-connected (old P rows B.K W)):=by
  have zq:(old P rows Z.K W).part J.quiet=1:=by
    rwa [density Z W,Poly.quiet_mul,Poly.pass_part _ (quiet Z W),one_mul] at whole
  have bq:(old P rows B.K W).part J.quiet=1:=(vacuum B Z W).symm.trans zq
  rw [density Z W,density B W,FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part _ (quiet Z W)) zq,
    FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part _ (quiet B W)) bq,
    FormalOPE.RG10.PolyUtil.conn_pass _ (quiet Z W),FormalOPE.RG10.PolyUtil.conn_pass _ (quiet B W)]
  unfold exponent;rw [Finset.sum_sub_distrib];abel

end YM.Integration.WilsonSeparatedOriginalLedgerGas
