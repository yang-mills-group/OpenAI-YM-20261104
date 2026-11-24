import YM.Integration.WilsonSeparatedOriginalSlabTranslation
import YM.Integration.WilsonSeparatedOriginalSlabWave

/-! Common child translations of the actual nonseparable pulse on any replica configuration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildWords
open Function Finset Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten MergeProof PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge} {C:Family G} {n N per:ℕ}

theorem key (d:ℕ)(v:Palette C d)(i:Mark C d)(x y:Site (C.side N per))(U:Config G (C.side N per)):
    Pulse.key C N per d v i x (pull 1 y U)=Pulse.key C N per d v i (x+y) U:=by
  simp only [Pulse.key,Pi.smul_apply,stepUp,pull_pull,mul_one,affine]
  rw [show (1:Signed).act x=x by simp]

theorem address {n m:Side}(A:Ratio n m)(x y:Site n)(t:Site A.count):
    A.assemble (x,t)+A.embed y=A.assemble (x+y,t):=by
  unfold Ratio.assemble
  rw [show A.embed (x+y)=A.embed x+A.embed y from map_add A.root x y]
  abel

private theorem row (s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette C (s i))(x:Fin 3 → Site (C.side N per))
    (y:Site (C.side N per))(φ:Wave (Fin 3))(W:Fin 3 → Config G (C.side N per)):
    WilsonSeparatedOriginalReplicaWave.harpoon s v x φ (fun i=>pull 1 y (W i))=
      WilsonSeparatedOriginalReplicaWave.harpoon s v (fun i=>x i+y) φ W:=by
  change (∑a:(i:Fin 3)→Mark C (s i),(perform s (fun i=>(a i).1) φ).val 0 *
    ∏i:Fin 3,Pulse.key C N per (s i) (v i) (a i) (x i) (pull 1 y (W i)))=_
  refine sum_congr rfl (fun a _=>congrArg (fun l:ℂ=>(perform s (fun i=>(a i).1) φ).val 0*l) ?_)
  exact prod_congr rfl (fun i _=>key (s i) (v i) (a i) (x i) y (W i))

theorem copies (top:n ≤ N)(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette C (s i))(o:Fin 3 → Site (C.side n per))
    (c:Site (C.side n per))(φ:Wave (Fin 3))(W:Fin 3 → Config G (C.side N per)):
    WilsonSeparatedOriginalReplicaWave.scalp s v o top φ (fun i=>pull 1 ((C.S.toDepth top per).embed c) (W i))=
      WilsonSeparatedOriginalReplicaWave.scalp s v (fun i=>o i+c) top φ W:=by
  let A:=C.S.toDepth top per
  have each (t:Fin 3→Site A.count):(fun i=>A.assemble (o i,t i)+A.embed c)=fun i=>A.assemble (o i+c,t i):=funext (fun i=>address A (o i) c (t i))
  simp only [WilsonSeparatedOriginalReplicaWave.scalp,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  refine sum_congr rfl (fun t _=>congrArg (fun l:ℂ=>(∏i:Fin 3,ratioX A (s i))*l) ?_)
  exact (row s v (fun i=>A.assemble (o i,t i)) (A.embed c) _ W).trans (congrArg (fun y=>WilsonSeparatedOriginalReplicaWave.harpoon s v y _ W) (each t))

theorem physical (top:n ≤ N)(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette C (s i))(o:Fin 3 → Site (C.side n per))
    (c:Site (C.side n per))(φ:Wave (Fin 3))(W:Config G (C.side N per)):
    Pulse.scalp s v o top φ (pull 1 ((C.S.toDepth top per).embed c) W)=
      Pulse.scalp s v (fun i=>o i+c) top φ W:=by
  rw [←WilsonSeparatedOriginalReplicaRegularity.diagonal,←WilsonSeparatedOriginalReplicaRegularity.diagonal]
  exact copies top s v o c φ (fun _=>W)

end YM.Integration.WilsonSeparatedOriginalSlabChildWords
