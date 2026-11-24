import YM.OPE.Compatible.Draft.Quiver
/-!
# Noise channel canonical. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (S: StepData c f) (H: Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "Y"=> Keys G (Limb H)
def raysN (u:Y):= S.kernel.penalty* ∑ i:Limb H,G.price (put u i)
lemma restrictN : ContDiff ℝ ω (raysN S H (G:=G)):=by
      apply ContDiff.mul contDiff_const; apply ContDiff.sum; intro j hj; exact contDiff_iff_contDiffAt.mpr fun x=> YM.Stationary.matrix_price_jet (A:=fun u:Y=> put u j) (G.exp_jet.contDiffAt.comp (f:=fun p:Y=> p j) _ (contDiffAt_apply ..))
lemma roamsN (x:Y) : Tendsto (fun t:ℝ=> raysN S H (t•x)/t^2) (𝓝[≠] 0) (𝓝 (S.kernel.penalty* rainbow x x/2)):=by
       unfold raysN rainbow; simp_rw [mul_div_assoc, Finset.sum_div, real_inner_self_eq_norm_sq]; apply Tendsto.const_mul _; refine tendsto_finsetSum _ fun i _=> Work.F03.price_limit (V:=fun t=> put (t • x) i) (by simp) ?_; exact gemZero _ _ (zero_smul ..) x (by simpa only [one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const x)
lemma trackN : Radial.Stationary (raysN S H (G:=G)):=by
      have he:=Work.F03.hessian_of_limit ((restrictN S H (G:=G)).of_le le_top|>.contDiffAt) (Q:= fun x y=> S.kernel.penalty*rainbow x y) (roamsN S H) (fun x y z=>by simp only [rainbow,Pi.add_apply,inner_add_left,Finset.sum_add_distrib,mul_add]) (fun x y=>by unfold rainbow; rw [show ∑ i:Limb H,inner ℝ (x i) (y i)=_ from Finset.sum_congr rfl (fun _ _=> real_inner_comm ..)])
      exact ⟨((restrictN S H).of_le le_top|>.contDiffAt), he.1,fun x=>by unfold jet; rw [iteratedFDeriv_one_apply,he.2.1]; simp⟩
lemma bornN (x:Y):jet (raysN S H) 2 x=S.kernel.penalty* rainbow x x/2:=by
      let s:=raysN S H (G:=G); have hp:=((Pawn.trio (trackN S H)).stale x).limit; exact tendsto_nhds_unique hp ((roamsN S H x).mono_left (nhdsWithin_mono _ (show Set.Ioi (0:ℝ)⊆({0}:Set ℝ)ᶜ from fun x h=> Ne.symm (lt_of_lt_of_le h le_rfl).ne)))
def wellX (b:ℝ): Lid G (Limb H) where
      f:= raysN S H
      F:=trackN S H
      fmeas:=(restrictN S H).continuous.measurable
      bright:=by
            apply quadratic_min; intro x hx; rw [bornN]; exact div_pos (mul_pos S.kernel.penalty_pos (lt_of_le_of_ne (rainbow_nn _) (fun e=>hx (rainbow_zero x e.symm)))) (by norm_num)
      w:= fun x=> Real.exp (-b*raysN S H x)
      charm:= Real.exp_pos _
      coat :=((((restrictN S H).const_smul (-b)).exp).of_le le_top).contDiffAt
      gleams := (Continuous.measurable (Real.continuous_exp.comp ((restrictN S H).continuous.const_mul (-b))))
-- horizontal Stand at Fine chosen
def braveP (T:Plot (even_both S.ratio H))(t:S.Choices)(x:Tile G T.Free): Tile G (Limb H) := echo S H t (T.cite 1 x)
lemma bravePQ (T:Plot (even_both S.ratio H))(t:S.Choices)(h:S.patch.Branches S.kernel G):∃ u: Tile G T.Free→ Tile G (Limb H), Pilot.Hark u∧ u =ᶠ[𝓝 1] braveP S H T t:=by
      have he: S.prediction (1:Config G f) t=1:=funext fun i=> Push.settled S h _ t; refine Pilot.buildExt _ (funext fun i=> ?_) ?_
      · change S.prediction _ _ _=_; rw [T.dress1,coatOne,he]; rfl
      intro i; let P:=cloak (G:=G) μ ∘L (LinearMap.toContinuousLinearMap T.rollX); unfold braveP echo; simp_rw [← T.rollPut, ← cloak_e]; exact ((P.map_zero.symm ▸ Push.prediction_cont S h i.val t : ContDiffAt ℝ ω (fun v:Bid.Dir G f=>G.mat (S.prediction (represent v) t i.val)) (P 0)).comp 0 P.contDiff.contDiffAt)
end YM.OPE.Cascade.Rill
