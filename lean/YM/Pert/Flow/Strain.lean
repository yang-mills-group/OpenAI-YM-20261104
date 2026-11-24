import YM.Pert.Flow.ActionStep
/-!
An action-side trajectory compatible with the same Wilson ordered removal (matrix-side measuring coupling still needs separate comparison). No period coupling is chosen after changing the gauge group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology Set Extraction Asymptotics
open scoped Topology Classical
variable {G : Gauge} {C : Family G}

/-- Mesh and period sequences here further select only readings of `path.β` (on the same tables).
`β` in this structure is not claimed to be the inverse squared X-space coupling. -/
structure Strain (C : Family G) (F : Order) where
    first : Order
    row : ℕ → ℕ → ℝ
    β : ℕ → ℝ
    cutoff (i p) : Tendsto (fun j => C.path.β (F.mesh.after first.mesh j) p i) atTop (𝓝 (row i p))
    roof (i) : Tendsto (row i ∘ F.per.after first.per) atTop (𝓝 (β i))
    band (i) : C.path.levels.clock.hatBeta i / 2 ≤ β i ∧ β i ≤ 2*C.path.levels.clock.hatBeta i
    step (i) : |β (i+1)-β i-2*b0 G*logStride C i| ≤ (C.path.levels.params (i+1)).drift

private def width (C : Family G) (i) :=
    Set.Icc ((C.path.levels.clock.hatBeta i)/2) (2*C.path.levels.clock.hatBeta i)

private def constrained (C : Family G) (N p i : ℕ) : width C i :=
   if h : C.path.β N p i ∈ width C i then ⟨_,h⟩ else ⟨C.path.levels.clock.hatBeta i,(by
     have h := C.path.levels.fits.delayed i
     exact mem_Icc.mpr ⟨by linarith only [h], by linarith only [h]⟩
   )⟩

set_option maxHeartbeats 1000000 in
theorem strain_exists (hc : C.Makes) (F : Order) : Nonempty (Strain C F) := by
    let V:= ∀ i p : ℕ, width C i
    letI (i : ℕ) : CompactSpace (width C i) := isCompact_iff_compactSpace.mp (show IsCompact (width C i) from isCompact_Icc)
    let u (i : ℕ) : V := fun j p=>constrained C (F.mesh i) p j
    obtain ⟨Y,_,φ,hφ,hY⟩ := (isCompact_univ (X:=V)).isSeqCompact (s:=univ) (x:=u) (fun _=> Set.mem_univ _)
    let U:= ∀ i : ℕ, width C i
    let v (p : ℕ):U := fun i=>Y i (F.per p)
    obtain ⟨X,_,ψ,hψ,hX⟩ := (isCompact_univ (X:=U)).isSeqCompact (s:=univ) (x:=v) (fun _=>Set.mem_univ _)
    let col i p := (Y i p:ℝ)
    let B i := (X i:ℝ)
    let first:= Order.mk ⟨φ,hφ⟩ ⟨ψ,hψ⟩
    let mesh:= F.mesh.after first.mesh
    let τ:= F.per.after first.per
    have hf (j p): Tendsto (fun i=>C.path.β (mesh i) p j) atTop (𝓝 (col j p)) := by
         have hu := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hY j) p
         have he := (continuous_subtype_val (p:=(·∈width C j))).continuousAt (x:=Y j p) |>.tendsto.comp hu
         refine he.congr' ((mesh.cofinal.eventually_ge_atTop j).mono fun i hi=> ?_)
         exact show (constrained C (mesh i) p j).val =_
           from by have h : _ ∈ width C j := (hc.wilson.represents (mesh i) p j hi).band; simp only [constrained,dif_pos h]
    have hg i : Tendsto (fun k =>col i (τ k)) atTop (𝓝 (B i)) := (continuous_subtype_val (p:=(·∈width C i))).continuousAt (x:=X i) |>.tendsto.comp (tendsto_pi_nhds.1 hX i)
    refine ⟨first,col,B,hf,hg,fun i=> (X i).property,fun i=> ?_⟩
    have hl (u v:ℕ→ℝ) {y Y} (hu:Tendsto u atTop (𝓝 y)) (hv:Tendsto v atTop (𝓝 Y)) :
       Tendsto (fun t=> |u t-v t-2*b0 G*logStride C i|) atTop (𝓝 |y-Y-2*b0 G*logStride C i|) :=
        (continuous_abs.continuousAt (x:=_)).tendsto.comp ((hu.sub hv).sub tendsto_const_nhds)
    apply le_of_tendsto' (hl _ _ (hg _) (hg _)); intro k
    apply le_of_tendsto (hl _ _ (hf _ _) (hf _ _))
    rw [b0_normalizes]
    exact (mesh.cofinal.eventually_gt_atTop i).mono fun n hn=> (hc.wilson.steps (mesh n) _ i hn).2
end YM.Pert.Flow
