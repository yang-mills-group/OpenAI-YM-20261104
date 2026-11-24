import YM.MS.Wilson.Reflect
/-! Frame rotation in actual coordinates. At rank≥0 Plan. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Orient
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Bare Focus Landau Draft Sew Chart
open scoped Topology ContDiff
variable {n: Side} {G:Gauge}(k:Signed)

section
variable {R:Type} [AddCommGroup R][One R][DecidableEq R][Fintype R]
local notation "P"=>Four R

def affine (k:Signed) : City G P→L[ℝ] City G P:=ContinuousLinearMap.pi fun i=> fee k (some i.2) • ContinuousLinearMap.proj (purse k i)
omit [DecidableEq R][Fintype R] in
lemma affine_act (v:City G P) (x:Edge P): affine k v x=fee k (some x.2) • v (purse k x):=rfl
omit [DecidableEq R][Fintype R] in
lemma at_nation (v:City G P): nation (affine k v)= Lattice.pull k 0 (nation v):= by
    funext i; unfold Lattice.pull nation; cases he:k.flip i.2 <;> simp [Lattice.affine,Step.rotate,Step.read, Step.used,posDir,affine_act,fee,he,purse,shiftTerm,Next.SectorChange.exp_negative,sub_eq_add_neg]
omit [Fintype R] in
lemma affine_basis (x:Edge P)(i:G.ColorIndex): affine k (priv (purse k x,i))=fee k (some x.2) • priv (x,i):= by
    funext y; rw [affine_act]; by_cases he:y=x
    · subst y; simp [priv]
    have he' : purse k y≠purse k x:= (wayR k).injective.ne he; simp [priv,he,he'] -- maybe unused Pi
omit [Fintype R] in
lemma affine_dir (i:LightMode G P): affine k (direction (turn k i))= fee k i.1.1.1 • direction i:= by
    rcases i with ⟨⟨⟨_|a,_|_⟩,u⟩,x⟩ <;> first| exact affine_basis k _ u| simp [turn,direction]
-- All local analytic sections tied to finite Wick Fourier mesh in real link coordinates.
lemma pose_rule {f:City G P→ℝ}(h:germ f) : (pose k (region.symm (reads f))).val=reads (f ∘ affine k):= by
    unfold pose; rw [LinearMap.comp_apply, reads, reads, ink_ctrl_one _ _ h, ferry_pulls (U:=fun i=> fee k i.1.1.1 • direction i) (V:=(affine k) ∘ direction) (r:=turn k) ?hc h]; swap
    · intro i; obtain ⟨i,rfl⟩ := (axise k).surjective i; rw [Finset.sum_eq_single i, show (axise k) i=turn k i from rfl,only,one_smul]; exact affine_dir k i
      · intro b hb ht; rw [need _ (show (axise k) i≠turn k b from (axise k).injective.ne ht.symm),zero_smul]
      simp
    suffices graffiti (σ k) (region.symm (ink direction f))=region.symm (ink (fun i=> fee k i.1.1.1 • direction i) f) from by rw [this]
    exact Subtype.ext (tagged_scale f _ _ h)
-- home orientation incident shifts
omit [DecidableEq R] in
lemma home_ropes : pose k (sumHome (ropes G idRail (0:P)))=sumHome (ropes G idRail 0):= by
    have he (x:P): Lab.Shift x (ropes G idRail (0:P)) = ropes G idRail x:= by rw [show Lab.Shift x _= ropes G idRail (x+0) from sail_rope G (fun i:P=>x+i) (fun _ _=> (add_assoc ..).symm) 0]; simp
    rw [total_uses]; simp_rw [he,ropes,map_sum,map_sub,map_sum, pose_Aterm,pose_Cterm,Finset.sum_sub_distrib]
    have ht := Equiv.sum_comp (wayR k (R:=R)) (fun x=> ∑ i:G.ColorIndex,couple DotFlip (AHplus i x) (throat idRail x i)); simp_rw [Fintype.sum_prod_type] at ht; refine congr_arg₂ _ ?_ ?_
    · exact ht
    exact Equiv.sum_comp k.actEquiv.toEquiv (fun x:P=> ∑ i:G.ColorIndex, couple DotFlip (GHplus i x) (cog x i))
omit [DecidableEq R] in
lemma home_H : pose k (sumHome (weightH G (0:P)))=sumHome (weightH G 0):= by
    have he (x:P): Lab.Shift x (weightH G (0:P))=weightH G x:= by rw [show Lab.Shift x _=weightH G (x+0) from sweaterH G (fun i:P=>x+i) 0]; simp
    rw [total_uses]; simp_rw [he,weightH,map_sum];
    have ht := Equiv.sum_comp (wayR k (R:=R)) (fun x=> onedge x (Maurer.lac (G:=G)))
    simp_rw [Fintype.sum_prod_type] at ht; simp_rw [edgeH]; exact ht
end
lemma home_W (k:Signed) : pose k (sumHome (weightW G (drive n) 0))=sumHome (weightW G (drive n) 0):= by
    apply Subtype.ext; rw [show sumHome (weightW G (drive n) 0)= region.symm (reads (Chart.rent (drive n))) from Subtype.ext (allWeight G _),pose_rule k (rent_s (drive n))]; rw [show Chart.rent (G:=G) (drive n)∘ affine k=Chart.rent (drive n) from funext (fun i=>by rw [Function.comp_apply,original_W, at_nation,Wilson.energy_pull, ← original_W])]; rfl

-- reflection stencils across period for BulkTest
lemma atlas (n:Side) (x y) : wrap n (x+idRail y)=wrap n x+drive n y:= by rw [map_add,show wrap n (idRail y)=_ from wrap_step ..]; rfl
lemma vessel (n:Side)(G:Gauge): shown n (bosons G idRail 0)=bosons G (drive n) 0:= by rw [shown, az_t G _ (atlas n),map_zero]
lemma garment (n:Side)(G:Gauge): shown n (weightH G 0)=weightH G 0:= by rw [shown, sweaterH,map_zero]
lemma threads (G:Gauge) : stance (bosons G idRail 0) := by
   intro k; refine Eventually.of_forall fun n=> ?_; unfold docket; simp only [LinearMap.comp_apply,travel_t,moving_total,vessel]; unfold bosons; simp_rw [map_add,home_W, show (drive n)=idRail from rfl, home_ropes]
lemma scene (G:Gauge) : stance (weightH G 0) := by
   intro k; refine Eventually.of_forall fun n=>?_ ; unfold docket; simp only [LinearMap.comp_apply,travel_t,moving_total,garment,home_H]
end YM.MS.Native.Orient
