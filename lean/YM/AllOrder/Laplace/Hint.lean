import YM.AllOrder.Local.Render
import YM.AllOrder.Laplace.Tilt
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Matrix Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern YM.AllOrder.Local Vote
open scoped BigOperators MatrixOrder
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
    {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Poll.Body ι
variable {A B:X × Poll.Body ι →ℝ}{m:X→Matrix ι ι ℝ}{ρ:X→Poll.Body ι}
structure Accent (A B:X × Poll.Body ι→ℝ)(m:X→Matrix ι ι ℝ)(ρ:X→Poll.Body ι):Prop where
   steer : Steered A ρ
   poly : ContDiffAt ℝ ω B 0
   alive : ContDiffAt ℝ ω (Lantern.shade m) 0
   station : ∀ᶠ x in 𝓝 0,(m x).PosDef ∧ ∀ z: Poll.Body ι,fderiv ℝ A (x,ρ x) (0,z)=0 ∧ dotProduct z.ofLp (m x *ᵥ z.ofLp)=scratch (0,z) A (x,ρ x)
variable (T:Accent A B m ρ)
private lemma little_brush {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {F:X→E} (h : ContDiffAt ℝ ω F 0) (n:ℕ): ∃ r D : ℝ, 0< r ∧ 0<D ∧ ∀ x:X,‖x‖ < r →Brush n D 1 F x := by
 obtain ⟨s,hs,h₀,hc⟩:= h.contDiffOn' (m:=(↑n)) le_top (by simp)
 simp only [insert_eq_of_mem (Set.mem_univ ..),univ_inter] at hc
 obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (hs.mem_nhds h₀)
 obtain ⟨D,hD,E⟩:= Brush.compact (k:=n) (isCompact_closedBall (0:X) (r/2)) (f:=F) (fun i hi=> let h':= H (closedBall_subset_ball (half_lt_self hr) hi); (hc _ h').contDiffAt (hs.mem_nhds h'))
 exact ⟨r/2,D,half_pos hr,hD,fun i hi=> E _ (mem_closedBall_zero_iff.mpr hi.le)⟩
include T
lemma hollow (n:ℕ): ∃ u v p :ℝ, Golf A B ρ m n 1 u v p:= by
 obtain ⟨r,A',h',hA,h⟩:= little_brush T.steer.hard (n+2)
 obtain ⟨s,B',hs,hB,H⟩:= little_brush T.poly n
 obtain ⟨q,G,hq,hG,hG'⟩:= little_brush (T.alive.sub (contDiffAt_const (c:=Lantern.shade m 0))) n
 obtain ⟨w,C,hw,hC,hC'⟩:= little_brush T.steer.shape (n+2)
 let D:= A'+B'+G+C; let R:= min 1 (min r s); let V:=R/3; have hv:0<V:=div_pos (lt_min zero_lt_one (lt_min h' hs)) (by norm_num)
 have hg: ∀ᶠ x:X in 𝓝 0, ‖ρ x‖< V:= T.steer.shape.continuousAt.norm.eventually (gt_mem_nhds (show ‖ρ 0‖<V from (by rw [T.steer.map0,norm_zero]; exact hv)))
 obtain ⟨u,hu,hU⟩:= Metric.mem_nhds_iff.mp (T.station.and hg)
 let U:=min u (min V (min w q)); have hY: ∀ x:X,‖x‖ < U→ ‖x‖<u ∧ ‖x‖ < V ∧ ‖x‖ < w ∧ ‖x‖ <q:= fun x hx=> lt_min_iff.mp hx |>(fun h=> ⟨h.1,(lt_min_iff.mp h.2).1, (lt_min_iff.mp (lt_min_iff.mp h.2).2)⟩)
 have ht:V≤1:=by have hx: R≤1:=min_le_left ..; unfold V; linarith
 refine ⟨U,V,D,lt_min hu (lt_min hv (lt_min hw hq)),hv, ((min_le_right ..).trans ((min_le_left ..).trans ht)),ht,zero_le_one, fun x hx=> (hC' _ (hY _ hx).2.2.1).climb (by unfold D; linarith) le_rfl,fun z t x hz ht hb hx=> ?_,fun x hx z=> (hU (mem_ball_zero_iff.mpr (hY x hx).1)).1.2 z,fun x hx=> ⟨(hU (mem_ball_zero_iff.mpr (hY x hx).1)).1.1,(hG' _ (hY _ hx).2.2.2).climb (by unfold D; linarith) le_rfl⟩⟩
 have hp : ‖Lantern.visit ρ z t x‖<R:= by
   obtain ⟨h₁,h₂⟩:=ht; apply max_lt; · change ‖x.2‖<R; have h:= (hY _ hx).2.1; unfold V at *; linarith
   change ‖ρ _+t • x.1 • z‖<_; have h₃ : ‖ρ x.2‖<V:= (hU (mem_ball_zero_iff.mpr (hY _ hx).1)).2; have he: ‖t • x.1 • z‖ ≤ V:= by rw [norm_smul,norm_smul]; exact (mul_le_of_le_one_left (by positivity) ((Real.norm_of_nonneg h₁).trans_le h₂)).trans ((mul_le_of_le_one_right (norm_nonneg _) hz).trans hb.le)
   exact (norm_add_le ..).trans_lt (by unfold V at *; linarith only [he,h₃,hv])
 exact ⟨(h _ (hp.trans_le ((min_le_right ..).trans (min_le_left ..)))).climb (by unfold D; linarith only [hB,hG,hC]) le_rfl,(H _ (hp.trans_le ((min_le_right ..).trans (min_le_right ..)))).climb (by unfold D; linarith only [hA,hG,hC]) le_rfl⟩
lemma grace_nice (z:Y) (k:ℕ): ContDiffAt ℝ (↑k) (grace A B ρ m z) 0:= by
 obtain ⟨u,v,p,h⟩:= hollow T k
 have hg:= Vote.golf_high h (c:=1+‖z‖) (le_add_of_nonneg_right (norm_nonneg _)); exact (Lantern.compel (1*(1+‖z‖)) hg (x:=(0,0)) (norm_zero.trans_lt hg.pos) (norm_zero.trans_lt hg.pos') (by rw [one_mul]; exact le_add_of_nonneg_left zero_le_one)).smooth -- notation adv
lemma extend_foot {P:ℝ→X}(hb:Tendsto P (𝓝 0) (𝓝 0))(z:Y): ∀ᶠ t in 𝓝 (0:ℝ), let x:=(P t); A (x,ρ x+t • z)-A (x,ρ x)= t^2 * vote A ρ z (t,x):= by
 obtain ⟨u,v,p,h⟩:= hollow T 2
 have hh:= Vote.golf_high h (c:=1+‖z‖) (le_add_of_nonneg_right (norm_nonneg _)); filter_upwards [hb.eventually (ball_mem_nhds (0:X) h.pos),ball_mem_nhds (0:ℝ) hh.pos'] with i hi he
 have hx:=mem_ball_zero_iff.mp hi; exact funds A ρ z i _ (hh.station _ hx z).1 (fun j hj=> ((hh.color z j (i,P i) (by rw [one_mul]; exact le_add_of_nonneg_left zero_le_one) hj (mem_ball_zero_iff.mp he) hx).1.smooth.of_le (by norm_num)))
end YM.AllOrder.Laplace.SigmaP
