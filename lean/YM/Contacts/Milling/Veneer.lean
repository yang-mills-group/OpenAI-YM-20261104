import YM.Contacts.Milling.Spark
/-! Coarse chart rolling with Haar curvature fees -/
noncomputable section
namespace YM.Contacts.Milling.Spark
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n: Side}{S:StepData c f}
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ"=> insertion (plant T (G:=G))
local notation "FV" => Link G f
local notation "CV" => Link G c
local notation "Γ" => Active G T
local notation "ρ" => S.kernel.penalty
local notation "β" => Yard G S
local notation "Ω" => House.Dir β
-- Y reorientation need not injectivity proof clutter
abbrev buds (S:StepData c f) (i : Co c (Cellar G S.patch.L)): Yard G S:= (i.1,.inr i.2)
lemma offspring_free (i: β) : (∃ j,father S j=i)∨ ∃ j, offspring S j=i := by
  rcases i with ⟨x,v|v⟩; exact Or.inl ⟨(x,v),rfl⟩; let e:= splitCo S.ratio (Dye G); refine Or.inr ⟨e.symm (x,v), congr_arg (buds S) (e.apply_symm_apply _) ⟩ -- motive

def weave (S:StepData c f) : (Link G c × Link G f)→L[ℝ] House.Dir (Yard G S):= ContinuousLinearMap.pi fun i:Yard G S=> i.2.elim (fun q:Dye G=> (ContinuousLinearMap.proj (i.1,q)).comp (ContinuousLinearMap.fst ℝ _ _)) (fun u:Cellar G S.patch.L=> (ContinuousLinearMap.proj ((splitCo S.ratio (Dye G)).symm (i.1,u))).comp (ContinuousLinearMap.snd ℝ _ _))
@[simp] lemma grow (x:CV × FV): mature S (weave S x)=x.1:= rfl
@[simp] lemma blooms (x:CV × FV): teen S (weave S x)=x.2:= funext fun i=> (congr_arg x.2 ((splitCo S.ratio (Dye G)).symm_apply_apply i))
def templates (G:Gauge)(P:Patch)(q:Cellar G P.L) : Node (Mixed G P):=(0,.inr q)
def breathe (G:Gauge)(P:Patch)(r: Site P.L)(a:Axis): House.Dir (Cellar G P.L)→L[ℝ] G.Color:= LinearMap.toContinuousLinearMap { toFun v:= WithLp.toLp 2 fun i=> v (r, coord a,i), map_add':= fun _ _=> rfl,map_smul':= fun _ _=> rfl }
def luck (G:Gauge)(P:Patch)(Q: ChartRatio G)(x:House.Dir (Cellar G P.L)) : ℝ:= ∑ i: Site P.L, ∑ a:Axis, if seed i a then 0 else Real.log (fee Q (breathe G P i a x)/fee Q 0)
def gold (Q:ChartRatio G)(x:Ω): ℝ := ∑ i:Site c, luck G S.patch Q (load (templates G S.patch) i x)
lemma fpos0 {Q:ChartRatio G}(hQ:LocalRatio Q): 0<fee Q 0:= by unfold fee; rw [hQ.anchored,mul_one, max_eq_left hQ.scale.le]; exact hQ.scale
lemma luck_ana (P:Patch){Q:ChartRatio G}(h:LocalRatio Q): AnalyticAt ℝ (luck G P Q) 0:= by
  unfold luck; apply ContDiffAt.analyticAt (ContDiffAt.sum _); intro x _; refine ContDiffAt.sum ?_; intro a _; by_cases he:seed x a<;> simp only [he,↓reduceIte]; · exact contDiffAt_const
  let L:= breathe G P x a; apply ContDiffAt.log; exact ((ContDiffAt.comp (g:=fee Q) (f:=L) 0 (L.map_zero.symm ▸ Ratio.fee_smooth h) L.contDiff.contDiffAt).div_const _); simp [(fpos0 h).ne']
lemma luck_meas (P:Patch){Q:ChartRatio G}(h:LocalRatio Q): Measurable (luck G P Q) := by
  unfold luck; apply Finset.measurable_fun_sum; intro x _; refine Finset.measurable_fun_sum _ fun a _=>?_ ; by_cases he:seed x a<;> simp only [he,↓reduceIte]; exact measurable_const; exact (((Ratio.fee_meas h).comp (breathe G P x a).continuous.measurable).div_const _).log
abbrev sparkles (P : Patch)(Q:ChartRatio G)(r:ℕ) := aboard (templates G P) (words (luck G P Q) r)
def sparkling (S:StepData c f)(Q:ChartRatio G)(r:ℕ) := ashore (templates G S.patch) (words (luck G S.patch Q) r) c
lemma gold_ana {Q:ChartRatio G}(hQ:LocalRatio Q): AnalyticAt ℝ (gold (S:=S) Q) 0:= by
  apply ContDiffAt.analyticAt (ContDiffAt.sum _); intro i _; let L:=(load (templates G S.patch) i); exact ContDiffAt.comp (g:=luck G S.patch Q) (f:=L) _ (by rw [map_zero]; exact (luck_ana _ hQ).contDiffAt) L.contDiff.contDiffAt
lemma gold_meas {Q:ChartRatio G}(hQ:LocalRatio Q): Measurable (gold (S:=S) Q):= Finset.measurable_fun_sum _ (fun i _=>(luck_meas _ hQ).comp (load (templates G S.patch) i).continuous.measurable)
lemma gold_zero {Q:ChartRatio G} : gold (S:=S) Q 0=0:= by by_cases h:fee Q 0=0<;> simp [gold,luck,h]
lemma gold_spec {Q:ChartRatio G}(hQ:LocalRatio Q)(x:Ω)(r:ℕ): House.design (sparkling S Q r) x=Radial.jet (gold (S:=S) Q) r x:= by
  unfold gold sparkling; rw [words_read]; rw [Ion.loan_sum _ (fun i _=> ?_ )]; swap; · let L:= load (templates G S.patch) i; exact (AnalyticAt.comp (g:=luck G S.patch Q) (f:=L) (by rw [map_zero]; exact luck_ana _ hQ) (L.analyticAt _))
  apply sum_congr rfl; intro i _; rw [Garf.hash]; exact (woven (luck_ana _ hQ) (load (templates G S.patch) i) x r).symm
lemma scroll_gold {Q:ChartRatio G}(b:CV)(y:κ): gold (S:=S) Q (weave S (b,stash S T y))=∑ i:(T).Free, Real.log (fee Q (y i)/fee Q 0):= by
  let R:= S.ratio; let L (u: Site f)(a:Axis):ℝ:= if h:(u,a)∈(T).trunks then 0 else Real.log (fee Q (y ⟨(u,a),h⟩)/fee Q 0)
  let v:= weave S (b,stash S T y); let Z(x:Site c):= load (templates G S.patch) x v
  have hx (u:(T).Free): breathe G S.patch (R.residue u.val.1) u.val.2 (Z (R.parent u.val.1)) = y u:= by
     ext1 i; let a: Dye G:= (coord u.val.2,i); let p: Γ:=(u,i); have he:=plant_free S.ratio S.patch.odd_side G p; calc
       _ = v (buds (G:=G) S (S.ratio.parent u.val.1,(S.ratio.residue u.val.1,a))):= by change v (wrap c 0+R.parent u.val.1, Sum.inr (R.residue u.val.1,a))= _; rw [map_zero,zero_add]
       _ = teen S v (plant T p):= by change _=v (offspring S _); unfold offspring plant ix; rw [split_co]; rfl
       _ = y u i:= by rw [show teen S v=stash S T y from blooms _]; change (Ξ *ᵥ active T y) (plant T p)= _; simp [mulVec,dotProduct,insertion,(plant_inj T).eq_iff]; rfl
  calc
     _ = ∑ u:Site f,∑ a:Axis,L u a:= by
       rw [← Equiv.sum_comp R.splitSites.symm,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; apply sum_congr (by congr! <;> try rfl); intro r _; apply sum_congr rfl; intro a _; let q:= R.splitSites.symm (i,r); have hv:= R.assemble_res (i,r); have hQ:R.residue q=r:= hv; have hS : R.parent q=i:= R.assemble_parent (i,r); have hr : (q,a)∈(T).trunks ↔ seed r a:= (leaf_act («T»:=S.ratio) q a S.patch.odd_side).trans (hQ ▸ Iff.rfl); by_cases h:(q,a)∈(T).trunks; · rw [show L _ _= _ from dif_pos h,if_pos (hr.mp h)]
       let u:(T).Free:= ⟨(q,a),h⟩; have hh : breathe G S.patch r a (Z i)= y u:= by erw [← hQ,← hS]; exact hx u
       erw [show L _ _=_ from dif_neg h, if_neg (mt hr.mpr h)]; exact congr_arg (fun l:G.Color=>Real.log (fee Q l / fee Q 0)) hh
     _ = _:= by
       let I:= T; erw [← Fintype.sum_prod_type (f:= Function.uncurry L),← Fintype.sum_subtype_add_sum_subtype (fun i:Edge (Site f)=> i∈ I.trunks)]; rw [Finset.sum_eq_zero,zero_add]; swap; · intro j _; exact dif_pos j.property
       apply sum_congr (by congr! <;> try rfl); intro j _; exact dif_neg j.property
lemma gold_chart {Q:ChartRatio G}(hQ:LocalRatio Q) : ∀ᶠ y:κ in 𝓝 0,∀ b:CV, Real.exp (gold (S:=S) Q (weave S (b,stash S T y)))=jacobian Q y/jacobian (U:=(T).Free) Q 0:= by
   have hx (i:(T).Free): ∀ᶠ y:κ in 𝓝 0, 0<fee Q (y i):= (show ContinuousAt (fun y:κ=>fee Q (y i)) 0 from ContinuousAt.comp (g:=fee Q) (f:=fun p:κ=>p i) (Ratio.fee_smooth hQ).continuousAt (continuousAt_apply i 0)).eventually (lt_mem_nhds (fpos0 hQ))
   filter_upwards [eventually_all.mpr hx] with y hi u; rw [scroll_gold,Real.exp_sum]; simp_rw [Real.exp_log (div_pos (hi _) (fpos0 hQ)),Finset.prod_div_distrib]; rfl
lemma gold_jac_0 {Q:ChartRatio G}(hQ:LocalRatio Q) : 0<jacobian (U:=(T).Free) Q 0:= Finset.prod_pos fun _ _=>fpos0 hQ
lemma spice (v:Ω)(h:S.patch.Branches S.kernel G): Radial.jet (hot S) 2 v=(let x:= mature S v- flax G S *ᵥ teen S v; ρ*(x ⬝ᵥ x)/2):= by
   let a:= (mature S) v; let b:= teen S v; let μ:= arm G c 1 a; let y:=Work.F03.residual S (μ,arm G f 1 b); have he : a - (flax G S)*ᵥ b= flatten y := by
     suffices h: flax G S*ᵥ b= flatten (bills S (arm G f 1 b)) by rw [h]; rfl
     funext x; rcases x with ⟨i,j,k⟩; exact congr_fun (component_mul (G:=G) (probe S) b k) (i,j)
   have hf:= (torch_c (hot_ana h) (torch h)).2 v; change Radial.jet _ 2 _=ρ*((a - (flax G S)*ᵥ b) ⬝ᵥ _)/2; rw [hf]; change ρ * (∑ i:Body 1 c, ‖y i‖^2)/2= ρ*((a-(flax G S)*ᵥ b) ⬝ᵥ (a-(flax G S)*ᵥ b))/2; rw [he,flat_dot]; simp [real_inner_self_eq_norm_sq]
end YM.Contacts.Milling.Spark
