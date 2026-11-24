import YM.Comparison.Density.Mirrors.Profile
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Range
/-!
The earlier physical repetition construction has powerful mirror machinery too.
Use `Slide`'s Track actual-flag and derivative lemmas on our tracks, not an
assumption about new masks. Our gluing is centred (important for explicit
full Moves), uses no stalls and uses the SAME stencil instead of requiring
auxiliary `Offer`s at different periods to be physically available. Sides
can include even periods. Winding on the physical torus in other parts of
the densities is left alone.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors
open Function Lattice Wilson RG PhysicalNext.Repeat
open scoped Matrix.Norms.Frobenius Topology
variable {G : Gauge} {n : Side}

def track (k : Side) : Slide.Track (quad k) := ⟨wave k,fun v=> Or.inr (wave_step k v)⟩

def neighborhood (k : ℕ) (o : Site n) := halo k {o}

lemma neighborhood_iff (k : ℕ) (o x : Site n) : x∈neighborhood k o ↔ separation o x≤k := by
  simp [neighborhood, halo_spec]

lemma site_track (k : Side) (o : Site n) (x : Site (quad k)) :
    Slide.sites (track k) o x = wrap n (reflectAt k x)+o := rfl

lemma track_sites (k : Side) (o : Site n) (x : Site (quad k)) :
    separation o (Slide.sites (track k) o x) ≤ k.val :=
  Work.E08.separation_box_add o (reflectAt_mem ..)

def tiled (k : Side) (o : Site n) (U : Config G n) : Config G (quad k) := field k (expandAt o U)

lemma tiled_track (k : Side) (o : Site n) : tiled (G:=G) k o=Slide.shape (track k) o := by
  funext U e
  obtain ⟨x,i⟩:=e
  change (risen k x i).read _ _= _
  unfold risen
  split
  · rename_i h
    have he : Slide.grade (track k) (x,i)=1:= by
      change wave k _-wave k _=1; rw [h]; ring
    rw [Slide.shape,if_pos he]; rfl
  rename_i h
  have he : Slide.grade (track k) (x,i)= -1:= by
    change wave k _-wave k _= -1; rw [(wave_step k _).resolve_left h]; ring
  rw [Slide.shape,if_neg (he ▸ by norm_num),if_pos he,Step.neg_read]
  change (U (wrap n (reflectAt k x-step i)+ o,i))⁻¹=(U (Slide.sites (track k) o (x+step i),i))⁻¹
  rw [map_sub,Lattice.wrap_step,Slide.down _ _ x i he, site_track, sub_add_eq_add_sub]

lemma tiled_healthy (p : BudgetPoint) (k : Side) (o : Site n) (U : Config G n)
    (h : Healthy p.threshold (neighborhood k.val o) U) : flags p.threshold (tiled k o U)=∅ := by
  rw [tiled_track]
  exact Slide.allFlag _ o U _ (fun i => (neighborhood_iff ..).2 (track_sites ..)) _ p.threshold_pos.le h

lemma tiled_local (k : Side) (o : Site n) : LocalOn (neighborhood k.val o) (tiled (G:=G) k o) := by
  rw [tiled_track]; exact Slide.stable _ _ _ fun i => (neighborhood_iff ..).2 (track_sites ..)

lemma tiled_cont (k : Side) (o : Site n) : Continuous (tiled (G:=G) k o) := by
  rw [tiled_track]; apply continuous_pi; intro i; unfold Slide.shape; split_ifs <;> fun_prop
end YM.Comparison.Density.Mirrors
