import YM.AllOrder.Laplace.Rain
/-! # All order vacuum: verify known two-loop cancellations intrinsically. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical MatrixOrder
open Matrix Finset Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern Local Vote PositionX.Jet Shield Progress.StationaryScenes Green
open scoped BigOperators Matrix.Norms.Frobenius
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
local notation "Ω"=> ℝ × X
variable {A B:X×Poll.Body ι→ℝ}{ρ:X→Poll.Body ι}{M:X→Matrix ι ι ℝ}(h:Accent A B M ρ)
local notation "K"=>M 0
local notation "μ"=>sweep (M 0)⁻¹
variable (hb:∀ i j, ContDiffAt ℝ ω (fun x=>M x i j) 0) {c b:ℝ} (he:∀ z:ι→ℝ,dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z)(hc:Bottom (M 0) b)(hp:0<b)
local notation "R"=> Vote.moment A B ρ M
lemma feel (P: Tensor.T Ω ℝ 2) (x y:Ω): Tensor.diagonal P (x+y)+Tensor.diagonal P (-x+y) =2*(Tensor.diagonal P x+Tensor.diagonal P y):= by
 let E:= ContinuousMultilinearMap.ofSubsingleton ℝ (ℝ×X) ℝ (0:Fin 1); let S: Ω→L[ℝ]Ω→L[ℝ]ℝ:= (ContinuousMultilinearMap.ofSubsingletonₗᵢ ℝ (ℝ×X) (0:Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L P.curryLeft; have hh (u:Ω) : Tensor.diagonal P u= S u u:= congr_arg P (funext fun k=> Fin.cases rfl (fun _=>rfl) k)
 simp_rw [hh, map_add,map_neg,_root_.add_apply,_root_.neg_apply]; ring
include h he hc hb hp
lemma average_low (k:ℕ)(hk:k≤2)(t:ℝ)(x:X): Tensor.diagonal (R k) (t,x)= Tensor.diagonal (R k) (t,0):= by
 interval_cases k
 · simp
 · have he' : ∀ (p:Ω) (q:Ω), Tensor.diagonal (R 1) (p+q) = Tensor.diagonal (R 1) p+ Tensor.diagonal (R 1) q:= by intro p q; exact ((ContinuousMultilinearMap.ofSubsingleton ℝ (ℝ×X) ℝ (0:Fin 1)).symm (R 1)).map_add p q
   change Tensor.diagonal (R 1) _=_; rw [show (t,x)=((t,0):Ω)+(0,x) by simp, he', barren h hb he hc hp 1 (by decide), add_zero]
 have hh:= even_c h he 2 x t; have ht:= feel (X:=X) (R 2) ((t,0):Ω) (0,x); simp only [barren h hb he hc hp 2 (by decide) x] at ht; dsimp only [Prod.neg_mk,Prod.mk_add_mk] at ht; simp only [add_zero,neg_zero,zero_add,←hh] at ht; change Tensor.diagonal (R 2) (t,x)=Tensor.diagonal (R 2) (t,0); linarith
lemma cumul_first {k:ℕ}(hk:k ≤ 2)(t:ℝ)(x:X) : jet (Real.log ∘ Vote.aggregation A B ρ M k) k (t,x)=jet (Real.log ∘ Vote.aggregation A B ρ M k) k (t,0):= by
 let g:= Vote.aggregation A B ρ M k; have hu:ContDiffAt ℝ ω (Real.log ∘ g) 0:= Real.contDiffAt_log.mpr (show g 0≠0 from Vote.collect0.trans_ne one_ne_zero) |>.comp _ (terms_art R).contDiffAt; change jet (Real.log ∘ g) k (t,x)=jet (Real.log ∘ g) k (t,0)
 rw [← jet_entry (hu.of_le le_top), ← jet_entry (hu.of_le le_top)]; refine congr_arg (fun f:ℝ→ℝ=> someJ f k) (funext fun i=>?_); refine congr_arg Real.log ?_; change g (i • _) = g (i • _); unfold g aggregation terms; rw [Finset.sum_apply,Finset.sum_apply]; simp only [Prod.smul_mk,smul_zero]; exact Finset.sum_congr rfl fun j hj=> average_low h hb he hc hp j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hk) _ _
end YM.AllOrder.Laplace.SigmaP
