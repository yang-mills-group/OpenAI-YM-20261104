import YM.Integration.WilsonSeparatedOriginalSlabChildCell
import YM.Integration.WilsonSeparatedOriginalReplicaCubic

/-! The full seven-source scanner equals one original positive conditional on a rank-one input, after all three of its genuine scalar centers have been subtracted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabCenteredMean
open Function Finset MeasureTheory Lattice Wilson RG Source RG05Readout RG05Readout.Native RG05Readout.Address
open RG05Readout.Flatten RG05Readout.Pulse RG05Readout.Records
open WilsonSeparatedOriginalMarkedCubic PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
theorem algebra {A:Type*}[CommRing A][Algebra ℂ A](Q:A →ₗ[ℂ]ℂ)(unit:Q 1=1)(f:Fin 3 → A):
    Q (∏i:Fin 3,(f i-Q (f i) • 1))=cubic (fun a=>Q (∏i∈a,f i)):=by
  simp only [Fin.prod_univ_three,cubic,Finset.prod_singleton,
    Finset.prod_pair (f:=f) (show (0:Fin 3)≠1 by decide),Finset.prod_pair (f:=f) (show (0:Fin 3)≠2 by decide),
    Finset.prod_pair (f:=f) (show (1:Fin 3)≠2 by decide),
    sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,map_sub,map_smul,
    smul_eq_mul,unit,mul_assoc]
  ring

variable {G:Gauge}(R:Run G){N n u per:ℕ}
theorem original (s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(o:Fin 3 → Site (R.family.side n per))
    (top:n ≤ N)(opened:u+1 ≤ N)(U:Config G (R.family.side u per))(f:Fin 3 → Body):
    let F:=fun i:Fin 3=>Records.clinic R.family per N (s i) (v i) n (o i) (1,false) (f i)
    WilsonSeparatedOriginalReplicaScanner.sample R s v o top opened U (joint univ f)=
      actualTransport R.family (N:=N) (fun W=>∏i:Fin 3,(F i W-actualTransport R.family (N:=N) (F i) (Nat.le_of_succ_le opened) U)) (Nat.le_of_succ_le opened) U:=by
  let fine (i:Fin 3):ContinuousMap (Config G (R.family.side N per)) ℂ:=⟨Records.clinic R.family per N (s i) (v i) n (o i) (1,false) (f i),
    Records.clinic_cut ..⟩
  let Q:=WilsonSeparatedOriginalResidentExpectation.mean R opened U
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R opened le_rfl U
  have unit:Q 1=1:=by
    change (∫_:Config G (R.family.side N per),(1:ℂ) ∂WilsonMacroscopicRichFlatPosteriorLaw.law R N per opened U)=1
    simp
  have row:∀a:Finset (Fin 3),moment R.family id (fun i=>((fine i):_→ℂ)) (Nat.le_of_succ_le opened) U a=Q (∏i∈a,fine i):=by
    intro a;rw [WilsonSeparatedOriginalResidentExpectation.value]
    unfold WilsonSeparatedOriginalMarkedCubic.moment;congr 1;funext W;simp [ContinuousMap.prod_apply]
  rw [WilsonSeparatedOriginalReplicaScanner.measured,WilsonSeparatedOriginalReplicaCubic.clinic]
  change cubic (moment R.family id (fun i=>((fine i):_→ℂ)) (Nat.le_of_succ_le opened) U)=_
  rw [funext row,←algebra Q unit fine,WilsonSeparatedOriginalResidentExpectation.value]
  congr 1;funext W
  simp only [ContinuousMap.prod_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,
    smul_eq_mul,mul_one,Q,WilsonSeparatedOriginalResidentExpectation.value]
  rfl

end YM.Integration.WilsonSeparatedOriginalSlabCenteredMean
