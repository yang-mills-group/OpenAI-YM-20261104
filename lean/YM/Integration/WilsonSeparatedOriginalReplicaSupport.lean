import YM.Integration.WilsonSeparatedOriginalProfilePortfolio
import YM.RG05Readout.Pulse.Openly

/-! The genuine centered torus parent cells on the whole replicated conditional, before taking any absolute values. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalReplicaSupport
open Function Finset Matrix MeasureTheory Lattice RG Wilson RG05Readout Source Address Push Local Marker MergeProof
open RG05Readout.Flatten RG05Readout.Native RG05Readout.View RG05Readout.Pulse
open Extra.Histories PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{n u t N per:ℕ}

private theorem taboo (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette C (s i))(z:Fin 3→Site (C.side N per))
    (r:ℝ)(f:Wave (Fin 3))(y:Cloud (Fin 3))(absent:y∉tsupport f.val):
    WilsonSeparatedOriginalReplicaWave.harpoon (C:=C) (p:=per) (N:=N) s v z (fork r y f)=0:=by
  have he (i:ℕ):pie f 0 i y:=by
    unfold pie;rw [show iteratedFDeriv ℝ i f.val y=0 from notMem_support.mp (fun hh=>absent (support_iteratedFDeriv_subset i hh)),show (0:Wave (Fin 3)).val=(0:Cloud (Fin 3)→ℂ) from rfl];simp
  rw [WilsonSeparatedOriginalReplicaWave.stung s v z (fun i _=>he i),map_zero,map_zero]

theorem absent (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette C (s i))(h:n≤N){r cap:ℝ}(rp:0<r)(Ψ:Wave (Fin 3))
    (shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)(J:ℕ)(o:Fin 3→Site (C.side n per))
    (outside:o∉Pulse.area (C:=C) (p:=per) (b:=n) J)(reach:r*cap+2*C.S.a n≤C.S.a n*(J:ℝ))
    (z:E4)(hz:z∈Native.box):WilsonSeparatedOriginalReplicaWave.scalp s v o h (cropX Ψ o r z)=0:=by
  unfold WilsonSeparatedOriginalReplicaWave.scalp cropX
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,fly_fork]
  apply sum_eq_zero;intro w _
  rw [taboo];exact smul_zero _
  intro hP;apply outside;simp only [Pulse.area,Finset.mem_filter,Finset.mem_univ,true_and];intro i
  exact_mod_cast (le_of_mul_le_mul_left ((Pulse.understood h r Ψ rp shape w z hz o hP i).trans reach) (C.S.a_pos n))

theorem zero (R:Run G)(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(h:n≤N)(op:u+1≤N)
    {r cap:ℝ}(rp:0<r)(Ψ:Wave (Fin 3))(shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)
    (J:ℕ)(o:Fin 3→Site (R.family.side n per))(outside:o∉Pulse.area (C:=R.family) (p:=per) (b:=n) J)
    (reach:r*cap+2*R.family.S.a n≤R.family.S.a n*(J:ℝ))(g:Body)(V:Config G (R.family.side u per)):
    (∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V (cropX Ψ o r z))=0:=by
  rw [setIntegral_congr_fun (g:=fun _=>0) Pert.Cellular.cells_compact.measurableSet (fun z hz=>by
    rw [WilsonSeparatedOriginalReplicaScanner.measured,absent s v h rp Ψ shape J o outside reach z hz]
    simp [WilsonSeparatedOriginalReplicaMeasure.read]),integral_zero]

theorem radius (C:Family G)(n:ℕ){r cap:ℝ}(cp:0≤cap)(room:r≤C.S.a n):
    r*cap+2*C.S.a n≤C.S.a n*(⌈cap+2⌉₊:ℝ):=calc
  _≤C.S.a n*cap+2*C.S.a n:=add_le_add_left (mul_le_mul_of_nonneg_right room cp) _
  _=C.S.a n*(cap+2):=by ring
  _≤_:=mul_le_mul_of_nonneg_left (Nat.le_ceil _) (C.S.a_pos n).le

end YM.Integration.WilsonSeparatedOriginalReplicaSupport
