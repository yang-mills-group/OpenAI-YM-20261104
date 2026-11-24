import YM.MS.Local.ExactSpan
/-! # Grade spaces finite without Schwartz parameters -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open scoped Topology ContDiff
variable {A P D : Type} [Fintype A] [NormedAddCommGroup P] [NormedSpace ℝ P]
variable (P) (w c:A→ℤ) (h q:ℤ)

def Pane : Submodule ℂ (P→ℂ) where
   carrier := setOf fun f=> Plane.Shape f h
   zero_mem':= form_zero _
   add_mem' {_ _} hx hy:= (mem_setOf.mp hx).add (mem_setOf.mp hy)
   smul_mem' v _x hx:= (mem_setOf.mp hx).scalar v
variable [FiniteDimensional ℝ P]
private def into (j : ℕ) : Tensor.T P ℂ j→ₗ[ℝ] (Pane P j).restrictScalars ℝ where
   toFun x:= ⟨Tensor.diagonal x,form_diag x _ rfl⟩
   map_add' _ _:= rfl
   map_smul' _ _:= rfl

instance pane_finite : FiniteDimensional ℂ (Pane P h) := by
   rcases lt_or_ge h 0 with hx|hx
   · have he : Pane P h=⊥:= le_antisymm (fun f hf=> (Submodule.mem_bot _).mpr ((show Plane.Shape f h from hf).charge hx)) bot_le
     rw [he]; infer_instance
   lift h to ℕ using hx
   have he : FiniteDimensional ℝ ((Pane P (h:ℤ)).restrictScalars ℝ):= by
       refine .of_surjective (into P h) ?_
       rintro ⟨f,hf⟩; exact ⟨Tensor.coeff f h 0,Subtype.ext (show Tensor.diagonal (Tensor.coeff f h 0)=f from (Plane.Shape.form (j:=h) (show Plane.Shape f (h:ℤ) from hf)).symm)⟩
   exact Module.Finite.of_fg (Submodule.FG.restrictScalars_iff (R:=ℝ) |>.mp (Module.Finite.iff_fg.mp he)) -- check

instance seed_finite : FiniteDimensional ℂ (seed P w c h q) := by
    let T : seed P w c h q →ₗ[ℂ] Π i:A, Pane P (h-w i):= LinearMap.pi (fun i=> {
       toFun := fun x=> ⟨fun p=>x.val (i,p), (seedStar.mp x.property).form i⟩
       map_add' _ _:= rfl
       map_smul' _ _ := rfl }) -- indent
    exact .of_injective T fun x y h=> Subtype.ext (funext fun l=> congr_fun (congr_arg Subtype.val (congr_fun h l.1)) l.2)
instance tile_finite (r:ℕ): FiniteDimensional ℂ (tile P w c h q r) := by
    let I:=Fin r→ A; let v : I→ℤ := fun a=> h-(∑ i, w (a i))
    let J (i:I): tile P w c h q r→ₗ[ℂ] Pane (Fin r→P) (v i):= {
       toFun x:= ⟨fun p=>x.val (gaze i p), (tileCub.mp x.property).visible i⟩
       map_add' _ _:= rfl
       map_smul' _ _:= rfl }
    let T:= LinearMap.pi J
    refine .of_injective T (fun x y h=> Subtype.ext (funext fun v=> ?_))
    by_cases hv:v.length=r; · obtain ⟨a,p,rfl⟩:= discovered _ hv; exact congr_fun (congr_arg Subtype.val (congr_fun h a)) p
    exact ((tileCub.mp x.property).rank _ hv).trans ((tileCub.mp y.property).rank _ hv).symm
end YM.MS.Local
