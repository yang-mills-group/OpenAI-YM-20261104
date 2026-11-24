import YM.FormalOPE.RG10.Transit.Schedule

/-!
# Lenses on the actual addressed test regions (possibly many parts)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Lens
open Function Finset
open scoped BigOperators Classical
variable {X I : Type*} {T : Tape X}
    (A : Lens T) (Y : I → Lens T)

def region (v : Finset I) (h : v.Nonempty) : Lens T where
  m x := v.inf' h fun i=> (Y i).m x
  sign x := Finset.le_inf' _ _ fun i _ => (Y i).sign x
  path a b := by
    obtain ⟨i,hi,he⟩:= exists_mem_eq_inf' h fun i=> (Y i).m b
    rw [he]; exact (Finset.inf'_le _ hi).trans ((Y i).path ..)

lemma region_le {v : Finset I} (h:v.Nonempty) (i : I) (hi:i∈v) : (region Y v h).m ≤ (Y i).m := fun x => Finset.inf'_le (fun i=>(Y i).m x) hi
variable {v : Finset I} (h : v.Nonempty)
lemma under_region (he : ∀ i∈v,A.m ≤ (Y i).m) : A.m ≤ (region Y v h).m := fun x => Finset.le_inf' h _ fun i hi => he i hi x
lemma spaced_region {r} (he:∀ i∈v,A.Spaced (Y i) r) : A.Spaced (region Y v h) r := by
  intro a b; obtain ⟨i,hi,hr⟩ := Finset.exists_mem_eq_inf' h fun i=> (Y i).m b
  rw [show (region Y v h).m b=_ from hr]; exact he i hi a b

end YM.FormalOPE.RG10.Route.Lens
