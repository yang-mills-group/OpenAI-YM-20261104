import YM.Integration.WilsonReportHarvestResidentLog

/-! The normalized value of the specified held ledger, with its genuine signed singleton offsets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestLedgerFlat
open Function Finset Set Lattice RG Marker Wilson Push Extra.Histories Ac MergeProof Accent GridApprox.Nil Extra.Trajectories
open private restored from YM.Integration.WilsonReportHarvestResidentLog
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{J:Census V}

theorem returned (P:Rep G n)(rows:V → RG05Readout.Address.Three G n)(v:V → ℂ){o:V → Site n}
    {H:Support n → Config G n → Poly J}{K:Box n → Config G n → Poly J}
    (legal:Carton o H K P.p.threshold)(U:Config G n)(clear:flags P.p.threshold U=∅):
    let Z:=restore P (fun i W=>(rows i).2.1 W+v i) (fun i=>profile P.activities (rows i).2.2) H K
    let log:=Mach J (fun i=>(rows i).2.1 U+v i)+∑X,H X U
    ((P.eval U:ℂ)⁻¹ • Z U)=Poly.pass log ∧ connected ((P.eval U:ℂ)⁻¹ • Z U)=log:=by
  intro Z log
  let centered(i:V):RG05Readout.Address.Three G n:=((rows i).1,(fun W=>(rows i).2.1 W+v i),(rows i).2.2)
  have raw:Z U=(P.eval U:ℂ) • Poly.pass log:=restored P centered legal U clear
  have nz:(P.eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by
    rw [Rep.eval,Activities.gas_one _ _ clear,mul_one];exact (Real.exp_pos _).ne')
  have normalized:((P.eval U:ℂ)⁻¹ • Z U)=Poly.pass log:=by rw [raw,smul_smul,inv_mul_cancel₀ nz,one_smul]
  have silent:log.part J.quiet=0:=by
    dsimp only [log];rw [Poly.part_plus,mute,Poly.part_sum];simp only [(legal.exp _).1.sil];simp
  exact ⟨normalized,normalized ▸ FormalOPE.RG10.PolyUtil.conn_pass _ silent⟩

end YM.Integration.WilsonReportHarvestLedgerFlat
