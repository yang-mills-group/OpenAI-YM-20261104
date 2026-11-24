import YM.OPE.Compatible.Chain.Tug
/-!
# intended reference covariance
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
lemma coinage (v:Train r)(h:4≤r){u:ℝ}(hu:0<u):∃ A:Row M M,Whole A∧ ∀ n:Side, A.acts n=(major (ShellRow C v) n+u • 1)⁻¹:=by
      let D:= composeRows (cobound 0) (transRows (cobound 0)); let X:= minusRows (ShellRow C v) (scaleRows (-1) D); let P:= minusRows X (scaleRows (-u) (unitRow M)); let T:= Whole.boundary 0; have hD:Whole D:= T.prod T.flipped
      have hv:= Op_whole h v (C:=C); have hx:Whole X:= hv.minus (hD.weight _); obtain ⟨s,a,hp,hh⟩:= hx.minus ((Whole.coin M).weight (-u)); have ha : 0≤ max a 0:= le_max_right ..; let L:=FreeResolvent.margin M s (max a 0) u; have hℓ :0<L:=margin_pos M hp ha hu; have he (n): P.acts n=major (ShellRow C v) n+u • 1:=by
            rw [show P=_ from (show P=minusRows X (scaleRows (-u) (unitRow M)) from rfl), hx.less ((Whole.coin M).weight _), show X=minusRows (Op C v) (scaleRows (-1) D) from rfl, hv.less (hD.weight _),acts_scale,acts_scale, acts_unit, show D=composeRows (cobound 0) (transRows (cobound 0)) from rfl,T.acts T.flipped, acts_trans]; change _ - -1 • (grad n* (grad n)ᵀ) - -u • 1= _; simp [major,ShellRow]
      obtain ⟨A,hA,H⟩:= strip_resolvent P (u:=0) le_rfl hu hp ha (strip_mono hh le_rfl (le_max_left ..)) (fun n=>by rw [he]; simpa only [zero_add] using! ((show Gap (major (ShellRow C v) n) 0 from ⟨fun x=> by rw [zero_mul]; exact basin_nonneg h v x⟩).shift u)) (show L/2< L from half_lt_self hℓ)
      exact ⟨A,⟨_,_,half_pos hℓ,hA⟩,fun n=>by rw [H,he]; simp only [resolve,zero_smul,add_zero]⟩
section
variable {I X:Type*}(Z: I→Side){lp:Filter I}
lemma worldZ (h:Tendsto (fun i=>(Z i).val) lp atTop)(b:ℝ): Tendsto (fun i=>aquas (Z i)*b) lp (𝓝 0):= by convert! (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α:=ℝ) (by decide : 4≠0)).comp (tendsto_natCast_atTop_atTop.comp h))).mul_const b using 1; simp
lemma pocket (A:Row X X)(hv:Whole A)(h:Tendsto (fun i=>(Z i).val) lp atTop)(p q:X)(a: Cover)(x:(i:I)→Site (Z i)): Tendsto (fun i=> A.acts (Z i) (x i,p) (x i+wrap (Z i) a,q)) lp (𝓝 (A p q a)) :=by
      let f(i:I)(v:Cover) := if wrap (Z i) a=wrap (Z i) v then A p q v else 0; change Tendsto (fun i=> ∑' v:Cover,ite _ _ _) _ _; have hl(i):(∑' v:Cover, if x i+wrap (Z i) a=x i+wrap (Z i) v then A p q v else 0)=∑' v,f i v:=by unfold f; simp only [add_right_inj]
      simp_rw [hl]; let u(v:Cover):= if a=v then A p q v else 0; have he: (∑' v,u v)=A p q a:=by unfold u; simp
      rw [← he]; apply tendsto_tsum_of_dominated_convergence (hv.safe p q); swap; · apply Eventually.of_forall; intro i b; unfold f; split <;> simp
      intro k; by_cases hg:a=k; · unfold f u; subst k; simp; apply tendsto_const_nhds
      apply tendsto_const_nhds.congr'; have ht(c: Cover):∀ᶠ x in lp,lift (wrap (Z x) c)=c :=by
         -- any n sufficiently tall
         apply h.eventually (p:=fun n : ℕ=>∀ u:Side,u.val=n→lift (wrap u c)=c) ?_ |>.mono (fun i hi=>hi (Z i) rfl); filter_upwards [eventually_gt_atTop (2* Laurent.size c)] with n hn u hu; rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩; have hs: (c i).natAbs≤ Laurent.size c := Finset.single_le_sum (f:=fun i:Axis=> (c i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i); omega
      filter_upwards [ht a,ht k] with i ha hk; unfold f u; rw [if_neg hg, if_neg (fun e=> hg (ha ▸ hk ▸ congr_arg lift e))]
lemma pocket_fars (A:Row X X)(hv:Whole A)(p q:X)(x y:(i:I)→Site (Z i))(hf:Tendsto (fun i=> separation (x i) (y i)) lp atTop): Tendsto (fun i=> A.acts (Z i) (x i,p) (y i,q)) lp (𝓝 0):=by
      change Tendsto (fun i=>∑' b:Cover, if y i=x i+wrap (Z i) b then A p q b else 0) _ _; nth_rw 2 [← tsum_zero (α:=ℝ) (β:=Cover)] -- names
      apply tendsto_tsum_of_dominated_convergence (hv.safe p q); swap; · apply Eventually.of_forall; intro i b; split <;>simp
      intro b; let S:= Laurent.size b; apply tendsto_const_nhds.congr'; filter_upwards [hf.eventually (eventually_gt_atTop S)] with i h; rw [if_neg]; intro hg; change S<separation (x i) (y i) at h; rw [separation_comm, hg] at h; apply (not_lt_of_ge ?_ h); unfold separation; simp only [add_sub_cancel_left]; exact within_size .. 
end
end YM.OPE.Cascade.Terp
