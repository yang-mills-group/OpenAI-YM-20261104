import YangMills.WilsonProof.NativeSupport.JointCoatEnergy

/-! The real joint energy on a native co-sector uses one coarse ball of
radius 26 times the funded cover scale, even when the two endpoint frame
tags or the bond's predictor branch vary with the surrounding sector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointCoat
open Function Lattice RG RG.Patch Tree Wilson Finset Pressure Pressure.Stores Pressure.Tube
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Art Rotation
open scoped Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {F : Forest S.ratio}
    {T : Tube G S} {P : Teller G} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
    {X Y : Coat T F} {Z : Support c} {u v : Air f G} {k k' : Finset ℕ}

def zone (_S : StepData c f) (B : ℕ) (b : Bond c) : Support c := halo (26*B) {b.1}

theorem zone_cost (b : Bond c) (hB : 0<X.B) :
    coverNumber X.B (zone S X.B b)≤53^4 :=
  Corona.tile b.1 26 X.B hB

/-- The transition's dependency ball is already inside the charged source badge
whenever that fine source carries the embedded physical base of the bond. -/
theorem zone_in_badge (H : Cash W X.x μ L Q o C T R)
    (M : PhysicalNext.Repeat.Lotus.Leaf R) (b : Bond c)
    (root : S.ratio.embed b.1∈M.crest) :
    zone S X.B b⊆H.supportP (M.turn.badge S) := by
  change _ ⊆ Matter.areas R T Q.halo X.B (M.turn.badge S)
  rw [M.turn.badge_area]
  apply Corona.halo_mono (Nat.mul_le_mul_right X.B (show 26≤Q.halo by linarith [Q.buys]))
  apply Finset.singleton_subset_iff.mpr
  exact Finset.mem_image.mpr ⟨S.ratio.embed b.1,Finset.mem_union_left _ root,
    S.ratio.embed_parent b.1⟩

theorem energy_concur (A : Borough X Y Z u v k k' R) (room : Room P S T X.x)
    (b : Bond c) (inside : zone S X.B b ⊆ Z) :
    energy X (X.liftA R.beta u) b=energy Y (Y.liftA R.beta v) b := by
  have reach : predReach S.patch≤X.B := by
    change predReach S.patch≤radiusB X.x
    have paid := room.frame
    omega
  have large : 100≤X.B := room.sight.1
  have has (j : Site c) (near : separation b.1 j≤26*X.B) : j∈Z :=
    inside (halo_spec.mpr ⟨b.1,mem_singleton_self _,near⟩)
  have left : b.1∈Z := has _ (by rw [separation_self]; omega)
  have right : b.1+step b.2∈Z := has _ ((sep_step _ _).trans (by omega))
  have agree : AgreeNear S.ratio.parent b.1 (predReach S.patch)
      (X.input (X.liftA R.beta u)) (Y.input (Y.liftA R.beta v)) := by
    intro i hi
    apply A.quarters room
    intro j hj
    apply has j
    exact (separation_triangle b.1 (atEdge S i) j).trans (by
      change separation b.1 (atEdge S i)≤predReach S.patch at hi
      omega)
  have pred := prediction_near_eq (funds_branch room.accepted) _ _ X.k b agree
  have tag (U : Config G f) : S.prediction U X.k b=S.prediction U Y.k b := by
    have same : S.connector U X.k.1 b=S.connector U Y.k.1 b := by
      funext j
      simp only [StepData.connector,StepData.frames,A.site _ left,A.site _ right]
    simp only [StepData.prediction,same,A.bond _ left]
  unfold energy
  rw [A.actual b left right,pred,tag]

/-- All original body factors and every inserted bond agree on the common
enlarged region. Products can include several separated bonds. -/
theorem marked_term_concur (H : Cash W X.x μ L Q o C T R)
    (A : Borough X Y Z u v k k' R) (p : Molecule S) (J : Finset (Bond c))
    (h : Bond c→ℝ→ℂ) (old : H.unionP p⊆Z) (fresh : ∀ b∈J,zone S X.B b⊆Z) :
    (∏ b∈J,h b (energy X (X.liftA R.beta u) b))*
        (X.term R Q.table W o.a k Q.halo u p : ℂ) =
      (∏ b∈J,h b (energy Y (Y.liftA R.beta v) b))*
        (Y.term R Q.table W o.a k' Q.halo v p : ℂ) := by
  have room := H.laws.data.room
  apply congrArg₂ (·*·)
  · exact Finset.prod_congr rfl fun b bj => congrArg (h b) (energy_concur A room b (fresh b bj))
  apply congrArg Complex.ofReal
  exact Finset.prod_congr rfl fun i ip => A.complete room Q.buys i
    ((Finset.subset_biUnion_of_mem H.supportP ip).trans old) H.laws.intake o.a W Q.table

end YM.Integration.InletSusceptibility.JointCoat
