import YM.MSbar.Parma.Cameo
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "K"=>Joint F G
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "θ"=>Measuring.chart n G
local notation "⌂"=>Positions (Joint F G)
local notation "O"=> routeN S.ratio
variable {N m s p d:ℕ}{D Z A E r η B C a:ℝ} (α:ChartRatio G)(hα:LocalRatio α)
noncomputable def smelt (J:ChartRatio G)(x:G.Color):= Real.log (J.scale*J.J x)-Real.log (J.scale*J.J 0)
noncomputable def cord (F:Forest S.ratio) (x:F.Free)(G:Gauge) : Positions (Joint F G) →L[ℝ] G.Color:= (ContinuousLinearMap.proj x).comp ((tint G F.Free).toContinuousLinearMap.comp (pushG F))
lemma cheese (x:F.Free): ‖cord F x G‖ ≤ shade G:=by
    let L : Positions (Joint F G)→L[ℝ]Positions (Key F G):=pushG F; refine ContinuousLinearMap.opNorm_le_bound _ (shade_pos G|>.le) fun v=> ?_ ; change ‖(tint G _ (L v)) x‖≤ _; have hx:‖L v‖≤‖v‖:=by refine pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr fun i=> ?_; exact norm_le_pi_norm v (Sum.inr i)
    exact le_trans (norm_le_pi_norm _ _) ((tint_le _).trans (mul_le_mul_of_nonneg_left hx (shade_pos _|>.le)))
noncomputable def loan (n:ℕ)(α:ChartRatio G):=∑ i∈Finset.range (n+1), ‖iteratedFDeriv ℝ i (smelt α) 0‖
include hα
lemma wall (p:ℕ): Allows p (smelt α) 0 (loan p α):=by
    refine ⟨((contDiffAt_const.mul (hα.germ 0 (Metric.mem_ball_self hα.patch))).log (mul_pos hα.scale (hα.pos 0 (Metric.mem_ball_self hα.patch))|>.ne')).sub contDiffAt_const,fun i ht=> Finset.single_le_sum (f:=fun i=> ‖iteratedFDeriv ℝ i (smelt α) 0‖) (fun v _=> norm_nonneg _) (Finset.mem_range.mpr (by omega))⟩
noncomputable def signal (x:F.Free)(α:ChartRatio G) := smelt α ∘ (cord F x G)
noncomputable def feeJ (p:ℕ)(α:ChartRatio G) := Uniform.composeCost p (loan p α) (shade G)
lemma coin (i:F.Free) (p:ℕ): Allows p (signal F i α) 0 (feeJ p α):=by
    let L:= cord F i G; exact (show Allows p (smelt α) (L 0) (loan p α) from (map_zero L).symm ▸ wall α hα p).comp (allows_linear (cheese F i) (map_zero L|>.symm ▸ ((show ‖(0:G.Color)‖=0 from norm_zero).le.trans (shade_pos _).le):‖L 0‖ ≤ shade G)) -- syntax
open Next.SectorChange Bakery
lemma sting: swung F α =ᶠ[𝓝 0] fun x=>∑ i:F.Free,signal F i α x:=by
    have ht(i:F.Free): ∀ᶠ x:⌂ in 𝓝 0, α.scale*α.J ((cord F i G) x)≠0:=by
        let L:= cord F i G; have hx : ∀ᶠ x:⌂ in 𝓝 0,L x ∈ Metric.ball 0 α.radius:= L.continuous.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [map_zero]; exact Metric.mem_ball_self hα.patch)); exact hx.mono fun x h=> (mul_pos hα.scale (hα.pos _ h)).ne'
    filter_upwards [eventually_all.mpr ht] with x he
    unfold swung capitalJ pay signal smelt; simp only [Function.comp_apply,Finset.sum_sub_distrib]
    change Real.log _ - Real.log (∏ i:F.Free, α.scale*α.J _) = _; rw [Real.log_prod (fun x _=> ?_), Real.log_prod (fun x _=>?_)]; rfl; exact (mul_pos hα.scale (hα.pos 0 (Metric.mem_ball_self hα.patch))).ne'; exact he _
lemma origin (n:ℕ): ‖(0:G.Color)‖ ≤ loan n α:=by rw [norm_zero];exact (wall α hα n).nonneg
noncomputable def gate (F:Forest S.ratio) (x:F.Free): Site n:= x.val.1
lemma received (x:F.Free)(q:ℕ): Lumber (address F G) (gate F x) 0 (signal F x α) q (feeJ (q+1) α):=by
    have he:=coin F α hα x (q+1); refine native (fun x:F.Free=>signal F x α) _ _ _ _ _ _ (he.1.of_le le_top) (he.2 (q+1) le_rfl) (Eventually.of_forall (fun k=>?_ )); unfold signal Function.comp; refine congr_arg _ ?_; ext i; change (if _ then _ else _) = _; apply if_pos; simp [curbL,gate,address] -- check
lemma cast (a:ℝ)(s p m:ℕ)(ha:0≤a): Tokew (address F G) a s m 0 (potter (swung F α) (p+1)) (cities 4 0*rugL a (feeJ (p+1) α) s 0 p (cities (townCost G) 0)):=by
    have hx:0≤ feeJ (p+1) α:=by have hp:0 ≤ loan (p+1) α := (wall α hα _).nonneg; unfold feeJ Uniform.composeCost; have hh:= shade_pos G; positivity
    refine scaleBook (fun x:F.Free=>signal F x α) (fun i=>received F α hα i p) hx ha (swung F α) (sting F α hα) _ _ (Uniform.town _) ?_ _; let L:Edge (Site n)→Site n:=Prod.fst; exact (powerP n Axis).comp (f:=fun (x:F.Free)=>x.val) Subtype.val_injective
end YM.MSbar.Parma
