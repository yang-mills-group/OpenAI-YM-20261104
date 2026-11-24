import YM.LocalTaylorR2.Marker.Favorite
import YM.MergeProof.TeamCells
import YM.MergeProof.Palette
/-! # Multi marks integrated using real repressed Crew integrals.
  Views Kept on actual H.unionP; includes ALL Activity refs even when marks reuse.
  Terra and Sup budgets require all healthy halos on V represented.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

def tie (H:Cash W s μ L Q o C T R) (k:Finset ℕ)(i:Head S):Port.Test T:= fun _ X w=>
    let _:= H; let y:=worldZ X R.beta w; Polar.ember X o.a R W Q.table y (X.input y) w k Q.halo i
lemma crews (k:Finset ℕ) (i:Head S) : Kept H (H.supportP (i)) (tie H k i) := by
  constructor
  · intro F X X' w v ht hK Z hh hl hV
    have hr : Intake P T X.x R:= ht.symm ▸ H.laws.intake
    have he : Room P S T X.x:= ht.symm ▸ H.laws.data.room
    have hx : ground R T Q.halo X.B {i}⊆Z := by unfold ground Coat.B; rw [singleton_biUnion,ht]; exact hh
    have hp:= Borough.flops (show Borough X X' Z w v k k R from ⟨hl,(observe _).1 hV,fun _ _=> Iff.rfl⟩) he Q.buys hr o.a W Q.table hx
    simpa only [Polar.floating, Finset.prod_singleton] using! hp
  · intro E _ F X hx hk V Y w hp hv ht
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    exact bornB X (show ShellAccess S G X.x W X.width o.γ from (by rw [hx,hk]; exact H.laws.data.access)) hr Q.table_exists hp hv ht o.a Q.halo k i
  · intro F X hx hk hp z w
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    have h : ShellAccess S G X.x W X.width o.γ:=by rw [hx,hk]; exact H.laws.data.access
    have he := H.laws.data.funds
    have hy := Stained.fights X z h hr Q.halo k Q.table_exists
      (show 0<o.a*X.t from mul_pos o.large (show Room P S T X.x from hx.symm ▸ H.laws.data.room).fiery)
      (show 4*o.a*X.t<Q.table.radius from (by unfold Coat.t; rw [he.length_eq,hx]; exact H.laws.data.covers)) hp (worldZ X R.beta w) w (i)
    rw [← Stained.flight X z hr.ready h] at hy
    exact hy
  intro F X hx hk hp j b A E _ _ _ V x hq hz hA
  have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  have he : Room P S T X.x:= hx.symm ▸ H.laws.data.room
  have hh:= H.laws.data.funds
  have hw:=mul_pos o.large he.fiery; rw [← hx,← hh.length_eq] at hA
  let X' (t:F.Slice G×Air f G):= X.wrapY t.1; let F' t:=worldZ (X' t) R.beta t.2; let S' k y:= steer (X' k) b (fun i=> prune b (F' k i)) (V y)
  let Y t y:=vary (X' t) (V y); let T' t:= (X' t).input (F' t)
  let K t y:= sweepZ (Y t y) R.beta (S' t y)
  have hv: Zest S' x j := (hq.foreshadow (Y:=Prod.fst) F' hz).1
  let L' : Directions G f→ₗ[ℝ] Air f G := { toFun t:= WithLp.toLp _ (stand t),map_add' _ _:=rfl,map_smul' _ _:=rfl }
  have hK: Zest K x j := (((hv.plusminus (hq.settles (Y:=Prod.fst) he)).scalar (gStep R.beta)⁻¹).replay L'.toContinuousLinearMap)
  refine (hq.glassy (Y:=Prod.fst) T' he S' hv hr k Q.halo hw (show 4*o.a*X.t<Q.table.radius from (by unfold Coat.t; rw [hh.length_eq,hx]; exact H.laws.data.covers)) Q.table_exists i hK).congr ?_
  obtain ⟨p,hF⟩:= hq.sails
  filter_upwards [Silica.nearby X hz hq.lifts hF,hq.brews.1] with y hy hT t
  have ht: Drivable (X' t) b A (V y) :=⟨hy.good⟩
  let u:= F' t; let Z:= Y t y; let Ft:=steer (X' t) b u (V y)
  let w : Air f G:= course (X' t) b R.beta t.2 (V y)
  have hε:Transfer Z Ft (S' t y) (4*o.a*X.t):= ⟨(fruit (X' t) hz (V y) u (a:=4*o.a*X.t) (by unfold Coat.t; nlinarith only [hA,hz.warm])).both⟩
  have hv := conquered (X' t) hz _ u ht hw hA
  have h:= (plastic (X:=Z) hv hw).reeled he W Q.table k Q.halo hr i w
  symm; change Polar.ember Z o.a R W Q.table (worldZ Z _ w) (Z.input (worldZ Z _ w)) w k Q.halo i= _
  rw [show worldZ Z _ w=Ft from Silica.proceeds _ _ hr.positive _ _]; exact h.trans (Transfer.carries Z hε hw he hT _ _ _ _ Q.halo k i)
end YM.LocalTaylorR2.Orbit
