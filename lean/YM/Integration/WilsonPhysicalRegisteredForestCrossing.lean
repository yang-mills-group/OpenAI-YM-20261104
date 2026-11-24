import YM.Integration.WilsonPhysicalRegisteredForestAction
import YM.MSbar.Trust.Cycling

/-! The old angular variable for a bond crossing two coarse parents is priced
relative to another genuine bond with the same ordered parents. Both endpoints
keep exactly the same actual residual forest colours. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalRegisteredForestCrossing
open Lattice RG Wilson Tree MSbar.Heath OPE.Therm
open WilsonPhysicalAnchoredGauge WilsonPhysicalForestAnchor WilsonPhysicalLocalPlaquetteForest
open scoped Classical
variable {G:Gauge} {c f:Side} {S:StepData c f}

def parents (T:Forest S.ratio) (e:T.Free) : Site c × Site c :=
  (S.ratio.parent e.val.1,S.ratio.parent (e.val.1+step e.val.2))

/-- The old reference fine edge can carry an arbitrary group element. Only
its relative deviation against another actual bond has the small chart. -/
theorem pair (T:Forest S.ratio) (o:Site f) (D:ℕ)
    (period:2*radius D S.ratio.count.val<f.val) (u:T.Slice G) {τ:ℝ} (pt:0≤τ)
    (cold:T.drape u∈House.chilly (WilsonAxialWindow.cells o (radius D S.ratio.count.val)) τ)
    (e a:T.Free) (same:parents T e=parents T a)
    (near:∀b:T.Free,b=e∨b=a→separation o b.val.1≤D ∧ separation o (b.val.1+step b.val.2)≤D) :
    G.chord (u e*(u a)⁻¹)≤2*(area D S.ratio.count.val*τ) := by
  let g:=fun q:Site c=>transport (WilsonPhysicalAnchoredPaths.roads o) (T.drape u) (S.ratio.embed q)
  let changed:=fun b:T.Free=>g (parents T b).1 * u b * (g (parents T b).2)⁻¹
  have price (b:T.Free) (hb:b=e∨b=a):G.chord (changed b)≤area D S.ratio.count.val*τ:=by
    obtain ⟨base,next⟩:=near b hb
    have h:=field (S:=S) T o D period (T.drape u) pt cold (1:G.El) b.val base next
    rw [after_forest] at h
    simpa only [rotate,Lattice.gauge,one_mul,inv_one,mul_one,foot,canoe,anchored,T.off_tree,g,changed,parents] using h
  have group_eq: changed e*(changed a)⁻¹=g (parents T a).1 * (u e*(u a)⁻¹) * (g (parents T a).1)⁻¹:=by
    unfold changed;rw [same];group
  have bound:=G.chord_triangle (changed e) (changed a)⁻¹
  rw [group_eq,G.chord_conj,G.chord_inv] at bound
  have one:=price e (Or.inl rfl)
  have two:=price a (Or.inr rfl)
  linarith only [bound,one,two]

/-- A common coarse endpoint is a finite-distance spatial constraint at the
original finer scale, from the genuine stored forest routes. -/
theorem neighbors (T:Forest S.ratio) {x y:Site f} (he:S.ratio.parent x=S.ratio.parent y) :
    separation x y≤8*S.ratio.count.val := by
  have base (z:Site f):separation z (S.ratio.embed (S.ratio.parent z))≤4*S.ratio.count.val:=by
    have step:=Push.Uniform.stop_length z (T.hike z)
    rw [T.hike_root] at step
    exact step.trans ((T.hike_lower z).trans (T.bound z))
  have h:=separation_triangle x (S.ratio.embed (S.ratio.parent x)) y
  rw [he,separation_comm (S.ratio.embed (S.ratio.parent y)) y] at h
  have l:=base x
  rw [he] at l
  have k:=base y
  omega

end YM.Integration.WilsonPhysicalRegisteredForestCrossing
