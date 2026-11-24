import YM.MS.Color.Image
import YM.MS.Color.Mean
import YM.MS.Color.Invol
import YM.MS.Color.Pigment
import YM.MS.Color.Commutation
import YM.MS.Color.Group
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Coh
/-!
# Color invariant real jets and local exact terms

Use Følner? No: all G compact and same-G frame, integrate only fixed jets.
No passage through divergent graph with gauge average. Produces cohomology
with physical representatives too, not making gauge invariance an assumption
about changing basis after limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MeasureTheory
open Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {A P D E : Type} {F : Score G D P}
-- Need ∆ too later for exact decoupling. Present ordinary one Q for mean.

-- projection to real form separate. real property.
variable [NormedAddCommGroup P] -- not needed for mean_sym

lemma pale_linear (H: Score G D P) : pale (F+H)=pale F+pale H:= by unfold pale; rw [map_add]; simp only [smul_add]; abel
section local'
variable {F : Law G} {h q:ℤ} {r:ℕ}
lemma convert_carry (he:F∈Carry G h r): mean F∈Carry G h r:= by
    haveI : FiniteDimensional ℂ (Carry G h r):= by exact Module.Finite.of_injective (Submodule.inclusion (fare G h r)) (Submodule.inclusion_injective _)
    exact momentSpan _ G.probHaar (point_mass (F:=F)) (fun k=> repeat_carry k he)
-- Singlet for anchored (allows nonzero net) only.

theorem singular (hF:F∈ Bed G h 0 r) (he:natQ F=0) (ht:Bright F) :
   ∃ f∈ Carry G h r, ∃ H∈ Bed G h (-1) r, Bright f ∧ Bright H ∧ F=f+natQ H:= by
   obtain ⟨L,hL,H,hH,hp,hv,h'⟩:= class_free hF he ht.weight; have hu (H: Law G): mean (natQ H)=natQ (mean H):= mean_charge id
   refine ⟨pale (mean L),Submodule.smul_mem _ _ (add_mem (convert_carry hL) (stand (convert_carry hL))),pale (mean H),Submodule.smul_mem _ _ (add_mem (convert_sig hH) (staid (convert_sig hH))), hue hp, hue hv,?_⟩
   rw [← pale_identity ht.shadow,← mean_identity ht.color,h', map_add, hu,pale_Q,pale_linear]
end local'
end YM.MS.Color
