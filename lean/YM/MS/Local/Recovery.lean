import Mathlib.LinearAlgebra.Dual.Lemmas
import YM.MS.Local.Differential

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MatrixLet
open Landau Detect
open scoped Topology ContDiff
lemma point_recovery {A : Type} (H : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ H] (D:H→ₗ[ℂ]ℂ): ∃ s: Finset A, ∃ f:A→ℂ, ∀ F:H, D F=∑ i∈s,f i*F.val i := by
   let V (i:A): Module.Dual ℂ H:= { toFun x:=x.val i, map_add' _ _:=rfl,map_smul' _ _:=rfl }
   let P:= span ℂ (Set.range V)
   have hp : P.dualCoannihilator=⊥ := le_antisymm (fun x hx=> (Submodule.mem_bot _).mpr <| Subtype.ext (funext fun i=> (Submodule.mem_dualCoannihilator _).mp hx (V i) (show V i∈P from Submodule.subset_span (Set.mem_range_self i)))) bot_le
   have H' : P=⊤:= by
      apply Submodule.eq_top_of_finrank_eq
      rw [Subspace.dual_finrank_eq]; have hv:=Subspace.finrank_add_finrank_dualCoannihilator_eq P; rw [hp] at hv; simpa using hv
   obtain ⟨t,rfl⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp (show D∈P from H' ▸ Submodule.mem_top)
   refine ⟨t.support,t,fun F=> ?_⟩; simp only [Finsupp.sum,LinearMap.sum_apply]; rfl -- under sum
namespace BV
variable {G: Gauge}
abbrev Mover (G : Gauge) := Shift ℂ (field (Landau.parity (A:=Axis) (C:=G.ColorIndex)) (P:=FourP)) true
lemma par_seed {g : Grade G} {u q:ℤ} (hv:g∈ yields u q) i (hx:g i≠0): Landau.parity i.1=Local.parity q:= (split_parity _).trans (seed_test _ _ hv i hx)
end BV
end YM.MS.Local
