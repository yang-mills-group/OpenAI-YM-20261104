import YM.MS.Vista.ClosingV
/-!
# Period modulus.geometry.Request n/16 rather than stronger. Enough for comparisons. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{L:I→Side}{V:Visa I}{n:Side}
abbrev Gates (p:Lattice.Site n):= Lattice.lift p
lemma axis_max (v:Lattice.Site n):∃ i:Axis, pdist v=( Gates v i ).natAbs:= by obtain ⟨i,hi,hX⟩:= Finset.exists_mem_eq_sup' ( Finset.univ_nonempty (α:=Axis)) (fun i=>( Gates v i ).natAbs); exact ⟨ i, Eq.trans (Finset.sup'_eq_sup ..).symm hX ⟩ -- pdist sup not sup'? 
lemma tail_val (v:Lattice.Site n)(i:Axis): 2*( Gates v i ).natAbs ≤ n.val := by obtain ⟨h,hx⟩:= lift_centers v i; unfold Gates; omega
lemma sizeX (v:Lattice.Site n): 2*pdist v≤ n.val:= by obtain ⟨i,he⟩:= axis_max v; rw [he]; exact tail_val v i
lemma atτ (v:Lattice.Site n)(i:Axis): ‖embed ( Gates v ) i‖ = (( (Gates v i ).natAbs:ℕ): ℝ ):= by rw [ norm_eq_abs]; unfold embed; norm_cast; simp -- name check.To. not unfolding embed
lemma budget_geom (v:Lattice.Site n): ‖embed (Gates v)‖=(pdist v:ℝ):= by
    apply le_antisymm; · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; rw [atτ ]; exact_mod_cast component_le v i
    obtain ⟨i,hJ⟩:= axis_max v; rw [hJ,← atτ]; exact norm_le_pi_norm ..
lemma bornlf (v:Orbit.Half)(h:v≠0): pdist v=1:= by
    have he: 2* pdist v≤2:=sizeX v; suffices hx: pdist v≠0 from (by omega); intro hx; refine h ?_; rw [← wrap_lift v,show Lattice.lift v=0 from ?_,map_zero ]; funext i; obtain he:= component_le v i; rw [hx] at he; change Lattice.lift v i = 0; omega
lemma caress {t m:Side}(h:Ratio t m)(p:Lattice.Site t): pdist (h.root p)= h.count.val * pdist p := by
    obtain ⟨b,hb⟩:= axis_max p; obtain ⟨d,hd⟩:= axis_max (h.root p); have hh(i): Gates (h.root p) i= h.count.val * (Gates p i):= by simp only [Gates,Ratio.root_embed, Ratio.lift_embed, Pi.smul_apply,nsmul_eq_mul ];
    apply le_antisymm; · rw [hd, hh, Int.natAbs_mul, Int.natAbs_natCast ]; exact Nat.mul_le_mul_left _ ( component_le p d )
    rw [ hb ]; refine le_trans ?_ ( component_le (h.root p) b );  rw [show Lattice.lift (h.root p) b= _ from hh b, Int.natAbs_mul, Int.natAbs_natCast ]
lemma n_data (p:Lattice.Site n) : Gates ( wrap (periodN n) (Gates p))=Gates p:= by
    unfold Gates; refine lift_eq_iff.mpr ⟨rfl, fun i=>?_⟩; obtain ⟨ht,hh⟩:= lift_centers p i; rw [cap_val]; omega
lemma seeking (p:Lattice.Site n): pdist ( wrap (periodN n) (Gates p))= pdist p:= by unfold pdist; rw [show Lattice.lift (wrap (periodN n) (Gates p))= _ from n_data p] -- rewrite misses because Gates def
lemma altitude (p:Orbit.Zone n): pdist (p+p)= 2*pdist ( thumb n p ):= by rw [downward]; exact caress ..
lemma reduce (p:Orbit.Zone n): separation ( thin n ( ( τ_frame n ).parent p )) p = pdist ( thumb n p ):= by
    rw [ separation_comm, separation,show p-thin n _= wrap (periodN n) ( Gates (thumb n p)) from ?_, seeking ]; nth_rw 1 [ ← (τ_frame n).unpack_at p ]; exact add_sub_cancel_left .. 
-- geometry apex uses wrap and 1/16
end YM.MS.Vista
