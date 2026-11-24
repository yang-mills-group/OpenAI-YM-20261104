import YM.RegulatorIR.Calibration.Parity

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
section feed
variable {s:Scale}(q:Feeds) {p:ℕ}
-- increase 1/α by (v/2)t^{p+1}.
def dawn :Feeds:= ⟨fun _=>1,rfl,continuous_const,fun _=>zero_lt_one,contDiffAt_const⟩
lemma starts (n) : biases dawn.scale (n+1)=0:=by
 unfold biases; rw [show dawn.scale.beta=fun _=>1 from funext (fun t=>by change ((1:ℝ)⁻¹)^2= _;norm_num), tale_const, map_one]; simp
lemma start_at : Seconds dawn.scale p:=by
 intro i hi he; have h:i= (i-1)+1 :=by omega
 rw (occs:=.pos [1]) [h];exact starts _
-- increment at one order arbitrary
lemma step_feed (p:ℕ)(v:ℝ) : ∃ H:Feeds,Squares p (tale (H.scale.beta)) (tale q.scale.beta) ∧ biases H.scale (p+1)=biases q.scale (p+1)+v:=by
 let A:ℝ→ℝ:=q.dine⁻¹; let w:=v/2; let g:= fun x:ℝ=> x^(p+1); let f:= (fun _:ℝ=>w)*g; let b:= A+f
 have hA:A 0=1:=by change (q.dine 0)⁻¹=_; rw [q.origin,inv_one]
 have hp: Continuous A:= q.continuous.inv₀ (fun _=>(q.positive _).ne')
 have hx:ContDiffAt ℝ ∞ A 0:= q.smooth.inv (q.positive _).ne'
 have h:ContDiff ℝ ∞ g:=contDiff_id.pow _; have hh: ContDiff ℝ ∞ f:= contDiff_const.mul h
 have he: b 0=1:=by simp [b,hA,g,f]
 obtain ⟨r,hr⟩:= Feeds.admits (hp.add hh.continuous) (hx.add hh.contDiffAt) he
 let H:Feeds:= ⟨r.dine⁻¹,by simp [r.origin],r.continuous.inv₀ (fun x=>(r.positive x).ne'),fun x=>inv_pos_of_pos (r.positive x),r.smooth.inv (r.positive 0).ne'⟩
 have hk : H.scale.beta=r.dine^2:=by ext1 x;change (((r.dine x)⁻¹)⁻¹)^2= (r.dine x)^2; simp
 let T:Writing:= PowerSeries.X^ (p+1);let U:= PowerSeries.C w*T;let W:=tale A
 have ht : tale H.scale.beta=W^2+2*W*U+U^2:=by
    rw [hk]; rw [show tale (r.dine^2)=(tale (r.dine))^2 from Script.dictates (r.smooth.pow 2) (Outlook.script_pow (Script.actual r.smooth) 2),tale_eq (hx.add hh.contDiffAt) hr]; change tale (A+f)^2= _; rw [tale_add hx hh.contDiffAt, tale_mul (f:=fun _:ℝ=>w) (g:=g) contDiffAt_const (h.contDiffAt),tale_const, Script.dictates (show ContDiffAt ℝ ∞ g 0 from h.contDiffAt) (Script.predicts_pow (p+1))]; change (W+U)^2=_;ring
 have hV : tale q.scale.beta=W^2:=Script.dictates (hx.pow _) (Outlook.script_pow (Script.actual hx) _)
 have hP(i) (he:i≤p): coeff i U=0:=by unfold U T; rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]; split <;> first|omega|simp
 have hC(R:Writing)(i)(he:i ≤ p) : coeff i (R*U)=0:=by rw [coeff_mul]; apply sum_eq_zero; intro j hj; rw [hP j.2 (by have hh:= mem_antidiagonal.mp hj;omega),mul_zero]
 refine ⟨H,fun i hi=> ?_,?_⟩
 · rw [hV,ht,map_add,map_add,hC _ _ hi,pow_two U,hC U _ hi];simp
 unfold biases; rw [hV,ht,map_add,map_add,pow_two U, coeff_mul, coeff_mul]
 have ht : coeff (p+1) U=w:=by unfold U T;rw [coeff_C_mul, coeff_X_pow];simp
 rw [sum_eq_single_of_mem (0,p+1) (by simp) (s:=antidiagonal (p+1))]
 swap
 · rintro ⟨x,y⟩ hy hx;rw [show coeff y U=0 from hP y (by simp only [mem_antidiagonal] at hy; simp only [ne_eq,Prod.mk.injEq,not_and] at hx;omega)];exact mul_zero _
 rw [sum_eq_zero]; swap
 · rintro ⟨i,j⟩ hi; have ht:i+j=p+1:= mem_antidiagonal.mp hi; rcases le_or_gt i p with hp|hp; exact mul_eq_zero_of_left (hP i hp) _; exact mul_eq_zero_of_right _ (hP j (by omega))
 rw [add_zero]; simp_rw [show coeff (0,p+1).snd U=w from ht]; have hK : coeff 0 (2*W)=2:=by rw [show 2*W=W+W from by ring,map_add,show coeff 0 W=1 from (tale_base).trans hA];norm_num
 rw [show coeff 0 (2*W)=2 from hK]; unfold w;ring
end feed
end YM.RegulatorIR.Calibration
