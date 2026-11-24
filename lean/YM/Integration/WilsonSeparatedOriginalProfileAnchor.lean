import YM.RG01.Slack
import YM.RG05Readout.Pulse.Openly
import YM.RG05Readout.Halls.Kin

/-! Geometry of a contributing three-site parent in the original profile sum.
A common shift by the embedded parent of the first site retains all residues. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalProfileAnchor
open Filter Finset Lattice RG Source RG05Readout MergeProof Wilson
open scoped Classical BigOperators
variable {G:Gauge}

theorem separation_of_area (C:Family G){n per J:ℕ}{o:Fin 3→Site (C.side n per)}
    (inArea:o∈Pulse.area (C:=C) (p:=per) (b:=n) J)(i k:Fin 3):
    separation (o i) (o k) ≤ 2*J:=by
  simp only [Pulse.area,Finset.mem_filter,mem_univ,true_and] at inArea
  calc separation (o i) (o k) ≤ separation (o i) 0+separation 0 (o k):=separation_triangle .. 
       _ ≤ 2*J:=by rw [separation_comm 0 (o k),two_mul];exact add_le_add (inArea i) (inArea k)

def anchor {c f:Side}(A:Ratio c f)(o:Fin 3→Site f):Fin 3→Site f:=
  fun i=>o i+A.root (-(A.parent (o 0)))

theorem assembled {c f:Side}(A:Ratio c f)(o:Fin 3→Site f)(i:Fin 3):
    anchor A o i=A.assemble (A.parent (o i)-A.parent (o 0),A.residue (o i)):=by
  change o i+A.root (-(A.parent (o 0)))=A.root (A.parent (o i)-A.parent (o 0))+wrap f (lift (A.residue (o i)))
  rw [map_sub,map_neg]
  calc _=(A.root (A.parent (o i))+wrap f (lift (A.residue (o i))))+(-A.root (A.parent (o 0))):=
         congrArg (fun y:Site f=>y+(-A.root (A.parent (o 0)))) (A.unpack_at (o i)).symm
       _=_:=by abel

theorem located {c f:Side}(A:Ratio c f)(o:Fin 3→Site f):
    A.parent (anchor A o 0)=0 ∧
    (∀i,A.parent (anchor A o i)=A.parent (o i)-A.parent (o 0)) ∧
    (∀i,A.residue (anchor A o i)=A.residue (o i)) ∧
    ∀i k,separation (anchor A o i) (anchor A o k)=separation (o i) (o k):=by
  refine ⟨?_,?_,?_,fun i k=>separation_translate ..⟩
  · rw [assembled,A.assemble_parent,sub_self]
  · intro i;rw [assembled,A.assemble_parent]
  · intro i;rw [assembled,A.assemble_res]

theorem collar (A:Levels G)(hG:G.Simple)(J:ℕ):
    ∀ᶠn:ℕ in atTop,2*J ≤ 1024*((A.budget n).B)^2:=by
  filter_upwards [(Real.tendsto_log_atTop.comp (RG01.Physical.hats hG A)).eventually_ge_atTop
    (((2*J:ℕ):ℝ)+1)] with n hn
  change ((2*J:ℕ):ℝ)+1 ≤ Real.log (A.clock.hatBeta n) at hn
  have hc: (Real.log (A.clock.hatBeta n))^2 ≤ ((A.budget n).B:ℝ):=Nat.le_ceil _
  have hb:(2*J:ℕ)≤(A.budget n).B:=by
    exact_mod_cast (show ((2*J:ℕ):ℝ) ≤ ((A.budget n).B:ℝ) by nlinarith [sq_nonneg (Real.log (A.clock.hatBeta n)-1)])
  have hp:0<(A.budget n).B:=(A.budget n).B_pos
  nlinarith [Nat.mul_le_mul_left (A.budget n).B (show 1≤(A.budget n).B from hp)]

theorem priced (C:Family G)(hG:G.Simple)(J:ℕ):
    ∀ᶠb:ℕ in atTop,∀per (o:Fin 3→Site (C.side b per)),
    o∈Pulse.area (C:=C) (p:=per) (b:=b) J → ∀shift:Site (C.side b per),∀i,
      coverNumber ((C.path.levels.budget b).B) ({o 0+shift,o i+shift}:Support (C.side b per)) ≤
        Ribbons.peepers C.path.levels b:=by
  filter_upwards [collar C.path.levels hG J] with b small
  intro per o chosen shift i
  let B:=(C.path.levels.budget b).B
  let x:=o 0+shift
  let y:=o i+shift
  have apart:separation x y ≤ (1024*B)*B:=by
    change separation (o 0+shift) (o i+shift) ≤ _
    rw [separation_translate];exact (separation_of_area C chosen 0 i).trans (small.trans_eq (by simp [B,pow_two,mul_assoc]))
  have cover:({x,y}:Support (C.side b per)) ⊆ halo ((1024*B)*B) {x}:=by
    intro z hz;rcases Finset.mem_insert.mp hz with h|h
    · subst z; exact halo_spec.mpr ⟨x,mem_singleton_self _,by simp⟩
    · rw [mem_singleton.mp h];exact halo_spec.mpr ⟨x,mem_singleton_self _,apart⟩
  exact (Corona.cover_mono cover B).trans (by simpa only [Ribbons.peepers,two_mul] using Corona.tile x (1024*B) B (C.path.levels.budget b).B_pos)

end YM.Integration.WilsonSeparatedOriginalProfileAnchor
