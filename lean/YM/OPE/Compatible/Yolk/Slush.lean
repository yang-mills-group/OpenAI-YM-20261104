import YM.OPE.Compatible.Yolk.Aperture
/-! receipts L polynomial charges -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
lemma walksIn (F:Forest S.ratio)(i:Bond f) : walksAt F i ⊆ halo (4*S.patch.L.val+1) {i.1}:=by
   let K:=4*S.patch.L.val+1; have hs(x y:Site f)(v:Walk)(hy:y∈ visits x v):separation x y ≤ v.length:= by
      induction v generalizing x y
      next=>simp_all [Lattice.visits]
      next j w ih=>
         simp only [Lattice.visits,List.mem_cons,List.length_cons] at *; rcases hy with rfl|hy; simp
         apply (separation_triangle _ (x+j.vec) _).trans; have ht:= ih _ _ hy; have he : separation x (x+j.vec)≤ 1:=by rw [separation_comm,separation,add_comm,add_sub_cancel_right,Step.vec]; split; rw [pdist_neg];exact pdist_step ..; exact pdist_step ..
         omega
   intro y hy; refine halo_spec.mpr ⟨_, Finset.mem_singleton_self _,?_⟩
   rcases Finset.mem_union.mp hy with hy|hy
   · exact (hs _ _ _ (List.mem_toFinset.mp hy)).trans (((F.hike_lower _).trans (F.bound _)).trans (Nat.le_succ _))
   apply (separation_triangle _ (i.1+step i.2) _).trans; have hh:= hs _ _ _ (List.mem_toFinset.mp hy); have he := (F.hike_lower (i.1+step i.2)).trans (F.bound _); have hg : separation i.1 (i.1+step i.2)≤1:=sep_step (c:=f) ..; change _ ≤ 4*S.patch.L.val at he; omega
lemma coverPeal (F:Forest S.ratio) (i: Bond f) (hM:4*S.patch.L.val+1≤ R.p.B): coverNumber R.p.B (walksAt F i) ≤ 1:=by
   have h:covers R.p.B (walksAt F i) {i.1}:=⟨(walksIn F i).trans (halo_mono hM le_rfl), ship_halo _ (by simp only [Ships,mem_singleton];rintro _ rfl _ rfl;exact .refl)⟩
   exact (list_cost R.p.B h).trans (card_singleton _|>.le)
def freight (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ x:ℝ):= (swing Q L μ 1 x 0).ceiling 0 0 0 0 / Q.goal L x
def tolls (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ x:ℝ):= (arcs Q L μ 1 x 0).ceiling 0 0 0 0 / Q.goal L x
lemma riseD (Q:YM.ConnectedActivityE6.Target G P)(L : Side) (h : 0<μ) : Rate G L 0 (freight Q L μ) ∧ Rate G L 0 (tolls Q L μ):=by
   let v x:=(arcs Q L μ 1 x 0).rootHit; have hv : Rate G L Q.rate v:= (((Q.rate_root (β:=1) (C:=0) L h).add (Rate.power.mul_right _)).add Rate.power)
   have hr: Rate G L Q.rate (fun x=>(swing Q L μ 1 x 0).rootHit):= ((Q.rate_root (β:=1) (C:=0) L h).add (Rate.power.mul_right _))
   have hb : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):= by
      refine Rate.power.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; rfl
   have hx : Rate G L 0 (fun x=>(1-sailUp Q L x)⁻¹):=by
      refine (Rate.const 2).compare ?_
      have he:= Q.stop
      filter_upwards [Rate.power.below (G:=G) (L:=L) (show Q.rate/2<0 by linarith) _ (by norm_num:(0:ℝ)<1/2)] with x hx
      have h:sailUp Q L x ≤ 1/2:= (le_abs_self _).trans hx
      have hp:1/2 ≤ 1-sailUp Q L x:=by linarith
      rw [abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hp)),abs_of_pos (by norm_num :(0:ℝ)<2)];exact (inv_anti₀ (by norm_num) hp).trans (by norm_num)
   constructor
   · have hh:= (((hr.mul hx).mul_left (Reserves.extract Q.ε 0 0 0)).mul hb); rw [add_zero,add_neg_cancel] at hh
     refine hh.congr (Eventually.of_forall fun x=>?_);unfold freight Mixed.Costs.ceiling Reserves.treeYield; rw [pow_zero,mul_one,Nat.cast_zero,mul_zero, div_eq_mul_inv];rfl
   have hh:= (((hv.mul_right (1-3/(4:ℝ))⁻¹).mul_left (Reserves.extract Q.ε 0 0 0)).mul hb);rw [add_neg_cancel] at hh; refine hh.congr (Eventually.of_forall fun x=>?_); unfold tolls Mixed.Costs.ceiling Reserves.treeYield; rw [pow_zero,mul_one,Nat.cast_zero,mul_zero,div_eq_mul_inv];rfl
lemma conformation (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ β x C:ℝ) : (swing Q L μ β x C).ceiling 0 0 1 0 / Q.goal L x = freight Q L μ x * Real.exp (-(Q.mark L μ x)):=by
   unfold Mixed.Costs.ceiling freight; unfold Mixed.Costs.ceiling; unfold Reserves.extract; simp only [Nat.cast_one,mul_one,Nat.cast_zero,mul_zero,sub_zero,zero_sub, Real.exp_zero]; change Reserves.polyPrice (swing Q L μ 1 x 0).reservePoly 0 * Real.exp (-Q.mark L μ x) * Reserves.treeYield (swing Q L μ 1 x 0).rootHit (swing Q L μ 1 x 0).q 0 / _ = _; ring

end YM.PhysicalNext.Repeat.Aroma
