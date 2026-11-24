import YM.AllOrder.Laplace.Iris
import YM.AllOrder.Haiku.Retreat
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical MatrixOrder
open Matrix Finset Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern Local Vote PositionX.Jet Shield Progress.StationaryScenes Green
open Wilson RG Tree Pressure Push.Uniform Gauge Precision Extra.Iteration
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f} {n k:ℕ}
variable (O: ChartRatio G)(T:Tube G S)(F: Forest S.ratio)(q:S.Choices){ρ: Bid.Dir G c→AxisChart G F}
local notation "K"=> Precision.Key F G
variable {σ C Λ:ℝ}(H:Push.Uniform.Before G σ C S.patch.J S.kernel (n+3))(hp: T.up.Bounds T.high σ C Λ)(ha: Bid.Larger (G:=G) S)(h:H.Service F T.high T.up ρ) (ho:LocalRatio O)
include H hp ha h ho
local notation "A" => Lapis.table F q T.up T.high
local notation "B" => Lapis.mist F O T.up
local notation "R" => Lapis.orbit (S:=S) F ρ
local notation "M"=> Lapis.gram F T.up T.high ρ q
local notation "X"=> Positions (Push.Uniform.Primary c G)
open Work.F05
lemma castle_room (i j: Precision.Key F G) : ContDiffAt ℝ ω (fun x:X=> M x i j) 0:= by
   let f:= fun x=> fderiv ℝ (tested F q T.high T.up x); let g:= fun x:Bid.Dir G c=> (x,ρ x); let C:= tint G (Exterior.Body 1 c); have hr:= h.critical; let hd:= Work.F05.curve_partial (F:=f) (Work.F05.curve_partial (hr.2.2 q).1); have he: ContDiffAt ℝ ω (fun x=> fderiv ℝ (f x) (ρ x)) 0:= by
     have ht : g 0=0:= Prod.ext rfl hr.1; exact ContDiffAt.comp (g:= Function.uncurry (fun x=> fderiv ℝ (f x))) (f:=g) 0 (ht.symm ▸ hd) (contDiffAt_id.prodMk hr.2.1)
   simp_rw [Lapis.gram,Lapis.glow,hessian, Matrix.of_apply,iteratedFDeriv_two_apply,Matrix.cons_val_zero, Matrix.cons_val_one]; exact ContDiffAt.comp (f:= C) (g:=fun x:Bid.Dir G c=> fderiv ℝ (f x) (ρ x) (frame F i) (frame F j)) 0 ((C.map_zero).symm ▸ (he.clm_apply contDiffAt_const |>.clm_apply contDiffAt_const)) C.contDiff.contDiffAt
lemma first_vote (x:X)(r:ℝ)(hk:k≤2): jet (Real.log ∘ Vote.aggregation A B R M k) k (r,x)=jet (Real.log ∘ Vote.aggregation A B R M k) k (r,0):= by
  have hv:= Lapis.wakes F q T.up T.high ρ σ C Λ H ha hp h (0:X) (norm_zero.trans_lt h.x_pos); let b:= (H.tables T.high S.patch).gap/2; have hb:= (H.receipt F q hp ha rfl rfl).1.pos_m; change 0< (H.tables T.high S.patch).gap at hb; exact cumul_first (accent_ready F O q T H ha hp h ho) (castle_room O T F q H hp ha h ho) hv.2.2.1 (show Bottom _ ((H.tables _ _).gap/2) from fun u=> by simpa only [dotProduct,pow_two] using hv.2.1 u) (half_pos hb) hk r x
open Kinetic.Port Kinetic
-- structural known geometry facts used at any clip. 
lemma intent_match (hT:ClassicalMatch F T.high T.low T.up T.down ρ)(k:ℕ)(hk:k≤4) : Radial.jet (Local.Pure.hard F T ρ q) k = Radial.jet (fun x:X=>mainTerm T.low T.down (Desk.night x)) k := by
   let L:=tint G (Exterior.Body 1 c); let A':= fun x=> tested F q T.high T.up x (ρ x); have hx:=hT k hk q; let f x:= mainTerm T.low T.down (represent (G:=G) (n:=c) x); ext1 x; change jet (A' ∘ L.toContinuousLinearMap) k x= jet (f ∘ L.toContinuousLinearMap) k x; rw [Kinetic.pivot _ A' _ hx.1,Kinetic.pivot _ _ _ hx.2.1]; unfold jet; rw [hx.2.2]
lemma soft_ball : Local.Pure.soft F T O ρ q =ᶠ[𝓝 0] ((Precision.thermal F q T.high T.up ρ O) ∘ tint G (Exterior.Body 1 c)) - (fun _=> Lantern.shade (M) 0) := by
   obtain ⟨u,v,p,hf⟩:= hollow (accent_ready F O q T H ha hp h ho) 2; -- Shellac.thermalP needs Golf n with u=v. shrink
   let y:=min u v; have H0:=golf_small hf (lt_min hf.pos hf.pos') (min_le_left u v) (min_le_right u v); filter_upwards [Shellac.thermalP F T O ρ q H0 ho h.critical.1] with x hx; unfold Local.Pure.soft; rw [Pi.sub_apply, show _ from hx]; rfl
end YM.AllOrder.Laplace.SigmaP
