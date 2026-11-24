import YM.OPE.Portfolio.Bookbind
/-!
# Horizon-zero exact charges
The Heard frame has nothing but unit in its leading space. Mars.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{H:History G}{N p i b:ℕ}{F:Labels.Frame G 0}
local notation "T"=> H.rep N p
set_option quotPrecheck false
lemma scalar (v:Label G 0) : ∃ q:ℂ,v=q • Labels.unit G 0:=by
    have he : gradePart (0,0) v=v:= by simpa [Finset.sum_range_succ] using (Labels.decompose v)
    exact Labels.scalar_grade 0 (he ▸ (gradePart_mem ..))
lemma one_at (i:F.Index) : i=0:=by
    obtain ⟨q,hq⟩:= scalar (F.basis i); by_contra hi
    have hp : F.coords (F.basis i) i=0:=by rw [hq,map_smul,F.coords_unit]; simp [Labels.Frame.e0,Pi.single_apply,hi,Ne.symm hi]
    rw [Labels.Frame.coords_basis] at hp; simp at hp
lemma one_core (v:F.Coeff) : F.core v=0:=by funext i; have h:= one_at i; change Function.update _ 0 0 i = _; rw [h,Function.update_self]; rfl
variable (B:SectionData F){A:Source.Hol G}{M:Voice F H p i} (h:Heard B H N p A i M)
lemma power_zero (v:F.Coeff) : v=v 0 • F.e0:= by funext i; rw [one_at i]; simp [Labels.Frame.e0]
include h
lemma units_id (v:F.Coeff) : M.index v=v:=by
    have he:= h.unit; simp only [Source.unitVec,pow_zero,one_smul] at he
    nth_rw 1 [power_zero v]; rw [map_smul,he]; exact (power_zero v).symm
lemma zero_ch (v:F.Coeff): M.charge v=0:=by
    have hx:= h.cone v; rw [one_core] at hx; apply le_antisymm ?_ (rem_nonneg ((h.earns v).2)); simpa only [Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using hx
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
