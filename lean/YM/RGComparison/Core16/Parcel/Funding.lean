import YM.RGComparison.Core16.Parcel.Coast

/-! # One investor, sign & real aperture supply BEFORE period.

Buys after individual postblock costs. (No assertion L costs uniform when increasing). Burner
used ORIENTATION incidence on actual captures. Admit at each true step to pay the accuracy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Parcel.Oven
open Function Set Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Matrix Push.AbsoluteSums.Animals
open Lumen Lumen.Planet PertExtension PertExtension.Series Tested Radial Therm
open Forge Forge.Hut Precision Exterior Push Push.BetaTransport Push.GridApprox Asymptotics
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{H:Patch}{K:KernelChoices}(P:Oven H)

structure Offers (X:Shelf G (PlaqAxes ⊕ Axis) P.Xways)(K:KernelChoices) :Prop where
   good:Good X
   purchase:∃ Q:ℝ, 0<Q ∧ X.sector=Hut.survey G H K Q ∧ ∀ x:G.Color,‖x‖≤ X.Q→∀ g:ℝ, amen X g → G.chord (G.lieExp (g • x))≤ Q*g
   citations i : EqOn (P.actual K i) (X.U i) (closedBall 0 X.R)
   illustration x:x∈closedBall 0 X.R→ P.Bright (G:=G) (K:=K) x

private lemma smoothen {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {f:E→ℝ}(hf:ContDiffAt ℝ ω f 0) :∃ g:E→ℝ,g=ᶠ[𝓝 0] f ∧ ContDiff ℝ ∞ g:=by
    let A:= {x| ContDiffAt ℝ ω f x}
    obtain ⟨b,hb,_,hB,hh,he⟩:= exists_contDiff_tsupport_subset (n:=⊤) (show A∈𝓝 0 from hf.eventually (by simp))
    let u: ContDiffBump (1:ℝ):= ⟨1/4,1/2, by norm_num, by norm_num⟩
    have h (x:ℝ)(hx:x∈closedBall (1:ℝ) (1/4)): u x=1:= u.one_of_mem_closedBall hx
    refine ⟨fun x=> u (b x)*f x,?_ ,contDiff_iff_contDiffAt.mpr (fun x=> ?_)⟩
    · filter_upwards [hB.continuous.continuousAt.eventually (show closedBall (1:ℝ) (1/4) ∈ 𝓝 (b 0) by rw [he]; exact closedBall_mem_nhds _ (by norm_num))] with x hx; rw [h (b x) hx, one_mul] -- x' use b x
    by_cases hx:x ∈ A
    · exact ((u.contDiff (n:=⊤)|>.comp hB).contDiffAt.mul ((show ContDiffAt ℝ ω f x from hx).of_le le_top))
    have hu : ∀ᶠ y in 𝓝 x,b y=0 := (notMem_tsupport_iff_eventuallyEq.mp (show x∉ tsupport b from fun he=>hx (hb he))) -- check
    refine (contDiffAt_const (x:=x) (c:=(0:ℝ))).congr_of_eventuallyEq ?_
    exact hu.mono (fun y hy=> show u (b y)*f y=0 by rw [hy,show u (0:ℝ)=0 from u.zero_of_le_dist (by norm_num [u,Real.dist_eq]),zero_mul])

private lemma velocity (G:Gauge):∃ A e:ℝ, 0<A ∧ 0<e ∧ ∀v:G.Color, ‖v‖≤ e→ G.chord (G.lieExp v) ≤ A*‖v‖:=by
    obtain ⟨C,hc,H⟩:= G.expDiff_zero.isBigO_sub.exists_pos
    obtain ⟨ε,hε,h⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (show {x:G.Color| ‖G.mat (G.lieExp x)-G.mat (G.lieExp 0)‖ ≤ C *‖x-(0:G.Color)‖} ∈ 𝓝 0 from H.bound)
    have hg:=G.colorScale_pos; refine ⟨C / G.colorScale, ε, by positivity,hε,fun v hv=>?_⟩
    unfold Gauge.chord; change _/G.colorScale ≤ _; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ hg.le; simpa only [G.mat_lieExp_zero, G.mat_one, Set.mem_setOf_eq,sub_zero] using (h (mem_closedBall_zero_iff.mpr hv))
private lemma restore_clasp (G:Gauge):∃ e:ℝ,0<e∧∀u:G.El,G.chord u<e→launch (G.curvature u)=u:=by
    obtain ⟨ε,hε,h⟩:=Metric.mem_nhds_iff.mp (show {x:G.El| _} ∈ 𝓝 (1:G.El) from @leaving G)
    have hg:=G.colorScale_pos
    refine ⟨ε/G.colorScale,by positivity,fun u hu=>h (Metric.mem_ball.mpr ?_)⟩
    change dist (G.mat u) (G.mat 1)<_
    rw [dist_eq_norm,G.mat_one]; exact (div_lt_div_iff_of_pos_right hg).1 hu -- direction
variable (h:H.Branches K G)
include h
lemma fund (q:ℝ)(hq:0<q) : ∃ X : P.Form G,X.Q=q ∧ Offers P X K:=by
    choose f hf hm using fun i=> smoothen (P.actual_hot h i)
    have hh:= (P.brighter h).and ((eventually_all.mpr hf).and (eventually_all.mpr fun i=> ((P.actual_hot h i).congr_of_eventuallyEq (hf i)).eventually (by simp)))
    obtain ⟨R,hR,he⟩:= Metric.nhds_basis_closedBall.mem_iff.mp hh
    obtain ⟨A,e,hA,hE,h⟩:= velocity G
    obtain ⟨a,ha,hc⟩:= restore_clasp G
    let δ:=min a (R/2); let u := min (e/q) (R/(2*q)); let Q:= A*q
    have hu: 0<δ:= lt_min ha (half_pos hR)
    have hk: 0<u:= lt_min (by positivity) (by positivity)
    have hv:u*q≤e := (le_div_iff₀ hq).1 (min_le_left ..)
    have hw:u*q<R:=by have h0:= show u*(2*q) ≤ R from (le_div_iff₀ (by positivity : 0<2*q)).1 (min_le_right ..); linarith only [hR, h0]
    let X:Shelf G _ _:= ⟨survey G H K Q, f, R, δ, u,q⟩
    refine ⟨X,rfl,⟨hR,⟨hu,(min_le_right ..).trans_lt (half_lt_self hR)⟩,⟨hq,hk,hw⟩,fun x h=> hc x (h.trans_le (min_le_left ..)),fun i x hx=>(he hx).2.2 i,hm,fun i=> ?_,fun i=>?_⟩, ⟨Q,by unfold Q; positivity,rfl, fun x hx g hg=>?_⟩,fun _ x hx=> ((he hx).2.1 _).symm,fun x hx=>(he hx).1⟩
    · exact (hf i).self_of_nhds.trans (P.zero (by assumption) _) -- h shadow
    · have he₀ : IsLocalMin (P.actual (G:=G) K i) 0:=Eventually.of_forall (fun x=> by change P.actual K i (0:Point G P.Xways) ≤ _; rw [P.zero]; exact P.nn x i; assumption)
      apply HasFDerivAt.congr_of_eventuallyEq _ (hf i); rw [← he₀.fderiv_eq_zero]; exact ((P.actual_hot (by assumption) i).differentiableAt (by simp)).hasFDerivAt
    have hp: ‖g • x‖ ≤ g*q:= by rw [norm_smul,Real.norm_of_nonneg hg.1]; exact mul_le_mul_of_nonneg_left hx hg.1
    exact (h _ (hp.trans ((mul_le_mul_of_nonneg_right hg.2 hq.le).trans hv))).trans ((mul_le_mul_of_nonneg_left hp hA.le).trans_eq (by unfold Q; ring))
end YM.RGComparison.Core16.Parcel.Oven
