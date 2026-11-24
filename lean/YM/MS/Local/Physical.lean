import YM.MS.Color.Image

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.Physical
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule
open Color Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {F: Law G} {r:ℕ} {h q:ℤ}
section spaces
open Color
lemma dark : Bright (0:Law G):= ⟨Koszul.Symm.zero,fun _=> map_zero _,map_zero _⟩
variable {F H: Law G}
lemma plus (hv : Bright F) (ht : Bright H): Bright (F+H):= ⟨hv.weight.add ht.weight,fun i=> by rw [map_add,hv.color,ht.color],by rw [map_add,hv.shadow,ht.shadow]⟩
lemma times (hv : Bright F) (x:ℝ): Bright (x • F) := by
   rw [show x • F=(x:ℂ) • F from rfl]; exact ⟨hv.weight.smul _, fun i=>by rw [map_smul,hv.color],by rw [map_smulₛₗ,hv.shadow]; simp⟩
variable (G)
def dual : Submodule ℝ (Law G) where
   carrier:= setOf Bright
   zero_mem':= dark
   add_mem' {_x _y} hx hy:= plus (Set.mem_setOf.mp hx) (Set.mem_setOf.mp hy)
   smul_mem' x _y hx:= times (Set.mem_setOf.mp hx) x
variable (h r q)
def Guide (H : Submodule ℂ (Law G)) := (H.restrictScalars ℝ) ⊓ dual G
def Allowed (h:ℤ) (r:ℕ) := Guide G (Carry G h r)
def Lease (h:ℤ) (r:ℕ) (q:ℤ) := Guide G (Bed G (h-q) q r)
def kills : (Law G) →ₗ[ℝ] (Law G):= natQ.restrictScalars ℝ
def Null (h:ℤ) (r:ℕ) : Submodule ℝ (Law G):= Allowed G h r ⊓ (Lease G (h-1) r (-1)).map (kills G)
end spaces
lemma byGuide (J: Submodule ℂ (Law G)) : F∈ Guide G J ↔ F∈ J ∧ Bright F := Iff.rfl
lemma lease_enough (G : Gauge) : Allowed G h r ≤ Lease G h r 0:= fun f h=> by refine (byGuide _).mpr ?_; have ht: f∈ Carry G _ _ ∧ _:= byGuide _ |>.mp h; exact ⟨by simpa using fare G _ _ ht.1,ht.2⟩
lemma null_subset (G:Gauge): Null G h r ≤ Allowed G h r:= inf_le_left
instance (G : Gauge) (h q:ℤ) (r): FiniteDimensional ℝ (Lease G h r q):= by
   let A:= (Bed G (h-q) q r).restrictScalars ℝ
   haveI : FiniteDimensional ℝ A:= Module.Finite.iff_fg.mpr (Submodule.FG.restrictScalars (R:=ℝ) (Module.Finite.iff_fg.mp (inferInstance : Module.Finite ℂ (Bed G (h-q) q r))))
   exact Module.Finite.of_injective (Submodule.inclusion (show Lease G h r q ≤ A from inf_le_left)) (Submodule.inclusion_injective _)
instance (G: Gauge) (h r): FiniteDimensional ℝ (Allowed G h r):= Module.Finite.of_injective (Submodule.inclusion (lease_enough G)) (Submodule.inclusion_injective _)
end YM.MS.Local.Physical
