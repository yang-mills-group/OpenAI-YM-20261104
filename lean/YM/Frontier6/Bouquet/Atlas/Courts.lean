import YM.Frontier6.Bouquet.Atlas.Examples

/-! Cradles for child footprints. Motion/measurement precision release across
 an interface between operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q: Ensemble}{i:P}
structure Court (i:P) where
   split : Ensemble
   legend : Burst i split
   root : Seats split
   clearance : ℝ
   pos : 0 < clearance
   radius : ℝ
   posradius : 0< radius
   gap : ∀ p∈dialogues legend.le i,∀ q∈ dialogues legend.le i,p≠q→ clearance+2*radius ≤ dist (root p) (root q)
namespace Court
abbrev small (Z:Court i) : Finset Z.split:=dialogues Z.legend.le i
variable (Z:Court i)
def chamber : Set (normal i.val):={x|∀ p∈ Z.small,∀ j∈p.val.val,house j x.val∈ ball (Z.root p) Z.radius}
lemma open_chamber : IsOpen Z.chamber:=by
   rw [show chamber Z=⋂ p∈ (Z.small:Set Z.split), ⋂ a:(p.val.val), {x:normal i.val|house (a:Slot) x.val∈ ball (Z.root p) Z.radius} by ext; simp [chamber]] -- goal maybe p∉ text simp
   exact isOpen_iInter_of_finite (fun p=> isOpen_iInter_of_finite fun hp=>isOpen_iInter_of_finite (fun a:(p.val.val)=> isOpen_ball.preimage ((house a.val).continuous.comp continuous_subtype_val)))
lemma exists_at (x: normal i.val)(hx:x≠0):∃ Z:Court i,x∈Z.chamber:=by
   obtain ⟨Q,hP,hh,hC⟩:=contestants i x hx
   let q := dialogues hP.le i; let u(j:Q):= house j.val.here x.val
   have h1(j k:Q)(he:j∈ q)(hp:k∈ q)(h:j≠k):0 < dist (u j) (u k):= dist_pos.mpr (fun hz=> h (hC he hp hz))
   have hv : ∀ᶠ r in 𝓝[>] (0:ℝ),∀ j∈q,∀ k∈q,j≠k→ r+2*r ≤ dist (u j) (u k):=by
       simp_rw [eventually_all]; intro j he k hh hk; apply eventually_nhdsWithin_of_eventually_nhds; refine (show Tendsto (fun r:ℝ=>r+2*r) (𝓝 0) (𝓝 0) from (by simpa [ContinuousAt] using (show ContinuousAt (fun r:ℝ=> r+2*r) 0 by fun_prop : Tendsto _ _ _))).eventually_le_const (h1 j k he hh hk) -- inspect
   obtain ⟨r,hr,h⟩:= ((show ∀ᶠ r in 𝓝[>] (0:ℝ),0<r from self_mem_nhdsWithin).and hv).exists
   exact ⟨⟨Q,hP,u,r,hr,r,hr,h⟩,fun p hp j hj=> (hh p hp j hj) ▸ mem_ball_self hr⟩
end Court
end YM.Frontier6.Bouquet.Atelier
