import YM.Lattice.Scale
import YM.MS.Vista.Leaf
import YM.PertExtension.OrbGeometry

/-! Separation from a whole reflected finite stencil by an original coarse-period translation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
namespace YM.Integration.WilsonMatrixTicketLanesReflectedSites
open Lattice MS MS.Orbit MS.Vista
open scoped Classical

private theorem four : pdist ((step (0 : Axis) : Site (4 : Side)) + step 0) = 2 := by decide

private theorem quarter {c f : Side} (ρ : Ratio c f) (hc : 4 ∣ c.val) :
    ∃ v : Site c, f.val = 2 * pdist (ρ.root v + ρ.root v) := by
  obtain ⟨t,ht⟩ := hc
  have hp : 0 < 4*t := ht ▸ c.property
  have htpos : 0 < t := by omega
  let τ : Ratio (4 : Side) c := ⟨⟨t,htpos⟩,ht⟩
  refine ⟨τ.root (step 0),?_⟩
  rw [← map_add,caress,← map_add,caress,four,ρ.exact_size,τ.exact_size]
  change 4 * t * ρ.count.val = 2 * (ρ.count.val * (t * 2))
  ring

/-- The distance to the inverted centre itself is proportional to the period. -/
theorem doubled {c f : Side} (ρ : Ratio c f) (four : 4 ∣ c.val) (a : Site f) :
    ∃ q : Site c,f.val≤4*pdist ((a+ρ.embed q)+(a+ρ.embed q)) := by
  obtain ⟨v,hv⟩:=quarter ρ four
  let A := a+a
  let V := ρ.root v+ρ.root v
  have triangle : pdist V≤pdist A+pdist (A+V) := by
    simpa only [neg_add_cancel_left,pdist_neg] using pdist_triangle (-A) (A+V)
  change f.val=2*pdist V at hv
  by_cases near : f.val≤4*pdist A
  · refine ⟨0,?_⟩; change f.val≤4*pdist ((a+ρ.root 0)+(a+ρ.root 0)); rw [map_zero,add_zero]; exact near
  · have far : f.val≤4*pdist (A+V) := by omega
    exact ⟨v,by simpa [A,V,add_comm,add_left_comm,add_assoc] using far⟩

/-- The reflected coordinate keeps the true reversed bond's unit displacement. -/
theorem window {c f : Side} (ρ : Ratio c f) (four : 4 ∣ c.val) (a : Site f) :
    ∃ q : Site c,∀ (u v : Site f) (i : Axis),8*(pdist u+pdist v+1)≤f.val →
      f.val ≤ 8*Lattice.separation (a+ρ.embed q+u) (PertExtension.Orb.reflect (a+ρ.embed q+v,i)).1 := by
  obtain ⟨q,hq⟩:=doubled ρ four a
  refine ⟨q,?_⟩; intro u v i width
  let x := a+ρ.embed q
  let z : Site f := (x+u)- (PertExtension.Orb.reflect (x+v,i)).1
  have cancel : z + -(u+v+step i) = x+x := by dsimp [z,PertExtension.Orb.reflect]; abel
  have front := pdist_triangle z (-(u+v+step i))
  rw [cancel,pdist_neg] at front
  have tail := pdist_triangle (u+v) (step i)
  have body := pdist_triangle u v
  have one := pdist_step (n:=f) i
  change f.val ≤ 4*pdist (x+x) at hq
  change f.val ≤ 8*pdist z
  omega

theorem physical (S : Schedule) {b N p : ℕ} (bN : b≤N) (a : Site (S.side N p)) :
    ∃ q : Site (S.side b p),∀ (u v : Site (S.side N p)) (i : Axis),
      8*(pdist u+pdist v+1)≤(S.side N p).val → (S.side N p).val ≤
        8*Lattice.separation (a+(S.toDepth bN p).embed q+u)
          (PertExtension.Orb.reflect (a+(S.toDepth bN p).embed q+v,i)).1 :=
  window (S.toDepth bN p) (S.side_four b p) a

end YM.Integration.WilsonMatrixTicketLanesReflectedSites
