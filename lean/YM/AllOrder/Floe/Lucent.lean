import YM.AllOrder.Floe.Sky
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
open Stationary Exterior Bloch Metric Stationary.Haiku
namespace Aero
variable {a A:ℝ}
lemma reachJ {f: Stationary.Space k →ℂ}(h:Firm σ C f): ‖iteratedFDeriv ℂ 2 f 0‖ ≤ (C/(σ/2))/(σ/4):= by
 let F:= iteratedFDeriv ℂ 1 f; have hp:= h.width_pos; let X:= Stationary.Space k
 have he {x:X} (hx:x∈ball (0:X) σ):x∈ Laurent.strip σ:= fun i=> (Complex.abs_im_le_norm (x i)).trans_lt ((norm_le_pi_norm ..).trans_lt (mem_ball_zero_iff.mp hx)); have hz x (hx:x∈ball (0:X) σ): ContDiffAt ℂ ω f x:=(h.analytic (he hx)).contDiffAt
 rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map, show σ/4=σ/2/2 by ring]; apply Stationary.chord (f:=F) (x:=0) (R:=σ/2) (by linarith) (fun v hv=>(hz _ (ball_subset_ball (by linarith only [hp]) hv)).differentiableAt_iteratedFDeriv (by simp)) (fun p hp=>?_) (mem_ball_self (by linarith)); unfold F; rw [norm_iteratedFDeriv_one]; exact Stationary.chord h.width_pos (fun i hi=>(hz i hi).differentiableAt (by simp)) (fun i hi=> h.2 _ (he hi)) hp
-- exact charge of a Picture.Ph. uses direct multi-letter from firm bound.
abbrev earth:= (axisCL (Keys 1)) ∘L roads.toContinuousLinearMap
abbrev tollN (u:ℝ):ℝ:= (1/(u/2))/(u/4)*‖earth (step 0 : Track)‖^2
lemma alpha_fee {T : Picture G 1} {C:ℝ} (h:∀ i j,Firm σ C (T i j)) (i:G.ColorIndex): |alphaPay i T| ≤ C*tollN σ:= by
 let f: Stationary.Space 1→ℂ:= T ![i,i] ![Exterior.coord (1:Axis),Exterior.coord (1:Axis)]; let v:Track:= step 0; let u:=fun _:Fin 2=> earth v; have ht:= h ![i,i] ![Exterior.coord (1:Axis),Exterior.coord (1:Axis)]; have hf:AnalyticAt ℂ f 0:=ht.analytic (ht.in_range (by simp)); have hh := ((hf.contDiffAt (n:=ω)).restrict_scalars ℝ).analyticAt
 have hp : leapTip T v 1 ![i,i] = (2:ℝ)⁻¹ • (iteratedFDeriv ℂ 2 f 0 u):=by
    change speedy (f ∘ earth) 2 v=_; unfold speedy Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,wired earth (by rw [map_zero]; exact hh),map_zero, ← (hf.contDiffAt (n:=(↑(2:ℕ):WithTop ℕ∞))).restrictScalars_iteratedFDeriv (𝕜:=ℝ)]; norm_num [Nat.factorial]; rfl
 rw [alphaPay,show leapTip _ _ _ _=_ from hp]; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_im,zero_mul, Complex.ofReal_re,sub_zero,← mul_assoc,mul_inv_cancel₀ (show (2:ℝ)≠0 by norm_num),one_mul]
 apply (Complex.abs_re_le_norm _).trans; have hv: ∏ i:Fin 2, ‖u i‖= ‖earth v‖^2:=by simp [u]
 apply ((iteratedFDeriv ℂ 2 f 0).le_opNorm u).trans; rw [hv,show C*(1/(σ/2)/(σ/4))=(C/(σ/2))/(σ/4) by ring]; exact mul_le_mul_of_nonneg_right (reachJ ht) (sq_nonneg _)
-- Tribute apex B.S.Condition for strict parent.
lemma live_alpha {F:Ink.Money.Bills (Coarse G)}(h:Haiku.Coat.Admits F){p : Picture G 1}(hp:∀ i j,Firm σ C (p i j))(hf:∀ n,Recorded p (F n) 0): TributeColor p σ C Universal:= charter (F:=fun i=> F (Ink.Echo.amplify three i)) (Ink.Echo.limitless three) hp (tendsto_const_nhds) (fun i=>by rw [mul_zero]; exact hf _) (fun i=> h.rise _) (fun i=> h.lull _) (fun i=> h.color _) (fun i s hU=> Eventually.of_forall (fun x=>h.garn _ s x))
-- decompose any T positive formula.Summability separate.Front. M base (Tipping). choose.
lemma alive (G:Gauge)(g:G.Simple) {σ M:ℝ}(hs:0<σ): ∃ (η A:ℝ),0<η∧ η≤σ∧0≤A∧∀ (F H:Ink.Money.Bills (Coarse G))(C:ℝ)(p:Picture G 1)(i:G.ColorIndex)(R:FaceRow), R.strip σ M → R.read 0=1 → 0≤C →0≤ M→(∀ i j,Firm σ C (p i j))→ Haiku.Coat.Admits F → Haiku.Coat.Admits H→ (∀ n,Recorded p (F n) 0) → (∀ n, Recorded (slots R G) (H n) 0)→
     ∃ Q: ℕ→Atom G 2, let a:=alphaPay i p; Charged Q η ((C+|a| *bedCharge σ M)*A) ∧ SymmetricAtoms Q ∧ Silent Q ∧ ∀ n, jet ((F n)-a • (H n)) 2 = jet (turnSeries (m:=n) Q) 2:= by
 obtain ⟨η,C,hh,hη,hC,H⟩:= veins G σ hs; refine ⟨η,C*inkCost G 1 η,hh,hη,mul_nonneg hC (inkCost_nonneg ..),fun F T A p i R hR hg hA hM hp hx hv hs' hT=>?_⟩
 let a:=alphaPay i p; let v:= p-(a:ℂ) • slots R G; let S(n:Side):= F n - a • T n; let X:=A+|a| * bedCharge σ M
 have he i : Recorded v (S i) 0 := Recorded.less (F:=F i) (H:=a • T i) (hx.rise _) (analyticAt_const.mul (hv.rise _)) (hs' i) ((hT i).weigh a (hv.rise _))
 have hι (i j) : Firm σ X (v i j):= by
    have hl:= ((hp i j).sub ((Firm.const (α:=Keys 1) hs (a:ℂ)).mul (slots_cost hs hR i j))); rw [Complex.norm_real,Real.norm_eq_abs] at hl; exact hl
 have hy : Haiku.Coat.Admits S:= by
    refine ⟨fun i=> (hx.rise _).sub (analyticAt_const.mul (hv.rise _)), fun i x=> ?_, fun i b=> (hx.color i b).sub ((hv.color i b).mono fun _ h=> congr_arg (a*·) h),fun n s x=>?_⟩; exact congr_arg₂ (fun x y:ℝ=>x-a*y) (hx.lull i x) (hv.lull i x); exact congr_arg₂ (fun x y:ℝ=>x-a*y) (hx.garn n s x) (hv.garn n s x)
 have H₀:= live_alpha hy hι he; have H' k j:= H₀.vanish g 1 0 (by decide) i (subtract_fee i (live_alpha hx hp hs') hR hs hg rfl) k j
 obtain ⟨Q,hQ,hO⟩:= H X 2 v (by unfold X; have hp:= bedCharge_nonneg (σ:=σ) hM; positivity) H₀.toFeatures H'
 let u:=Stationary.issue Q; obtain ⟨hF,hf⟩:= artery_funded hQ
 refine ⟨u, ?_, hf,fun i x=>?_,fun n=>?_⟩ -- deals with parent let. `Bs`: h\n
 · rw [← mul_assoc]; exact hF
 · let R: PathData G:= ⟨fun a i=> (0,Extra.Iteration.slot 0 a),u,(fun _=> Extra.Iteration.blank G 3),(fun _=> Extra.Iteration.blank G 4)⟩
   have hw:= issue_normal hQ.price hh hO R rfl i x; exact ⟨hw.1,hw.2⟩
 ext1 x; unfold jet; rw [← (show iteratedFDeriv ℝ 2 _ _ = iteratedFDeriv ℝ 2 (S n) 0 from aperture_eq (colors_align _ (hy.rise n) (Haiku.Coat.Admits.rotate hy n) v Q hQ hh (he n)))]
end Aero
end YM.AllOrder.Floe
