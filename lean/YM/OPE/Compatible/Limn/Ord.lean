import YM.OPE.Compatible.Limn.Sky
import YM.OPE.Compatible.Grafts.Barge
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Slant
/-!
# Panel budgets for every licensed F. Hessian evaluated on shape projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
variable {t r R B b ε:ℝ}{m:ℕ}
variable (S:StepData c f)(F: Forest S.ratio)
open Finset 
open Green (wt)
-- C=. Rate
abbrev pointK (p:Key F G): Site f:= p.1.val.1
abbrev farm (G:Gauge)(x:ℝ):= ((Fintype.card G.ColorIndex:ℝ)*(((Fintype.card Axis):ℝ)*Premium.overall x))
lemma farmPay (hp:0 < t)(i:Site f): ∑ j:Key F G, Wisps.rate (-t) (separation i (pointK S F j)) ≤ farm G t:=by
       have hy(k:Site f):Wisps.rate (-t) (separation i k)=(wt t k i)⁻¹:=by unfold Wisps.rate Green.wt; rw [separation_comm,neg_mul,Real.exp_neg]
       simp_rw [hy]; let q j:=(wt t j i)⁻¹; have hx: (∑ j:Site f,q j) ≤ Premium.overall t:= by simpa using Premium.lives 1 hp i
       change ∑ j:F.Free ×G.ColorIndex,q j.1.val.1 ≤ farm G t
       rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_const,nsmul_eq_mul,← mul_sum]; unfold farm; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _);
       have hm : (∑ j:F.Free,q j.val.1) ≤ ∑ j:Edge (Site f),q j.1:=by rw [←Finset.sum_image (f:=fun j:Edge (Site f)=>q j.1) (g:=fun j:F.Free=> j.val) (fun _ _ _ _ h=>Subtype.ext h)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> inv_nonneg.mpr (Green.wt_pos ..).le
       apply hm.trans; rw [Fintype.sum_prod_type]; simp_rw[sum_const,nsmul_eq_mul, ← Finset.mul_sum]; simp only [card_univ]; exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
lemma tillS {A:Matrix (Key F G) (Key F G) ℝ} (ht:0<t)(h:0 ≤ r)(hp:∀ (i j:Key F G), wt t (pointK S F i) (pointK S F j) * |A i j| ≤ r) : Pours A (pointK S F) (pointK S F) (t/2) (farm G (t/2)*r):=by
       simpa only [max_self] using pure ht h (p:=pointK S F) (L:=A) (q:=pointK S F) hp (farmPay S F (half_pos ht)) (farmPay S F (half_pos ht)) -- q binder names
lemma wt_span (x y i:Site f)(t:ℝ): wt t x y* (wt t x i)⁻¹ * (wt t y i)⁻¹ = Real.exp (t *((separation x y:ℝ)- (separation x i:ℝ)-(separation y i:ℝ))):=by unfold Green.wt; rw [← Real.exp_neg,← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; congr 1;ring
lemma eaten (x y i:Site f)(hp:0 < t): wt (t/2) x y*((wt t x i)⁻¹ * (wt t y i)⁻¹)≤ (wt (t/2) i x)⁻¹:=by
       have hv := Nat.cast_le (α:=ℝ).mpr (separation_triangle x i y); unfold Green.wt; rw [separation_comm i x]; rw [separation_comm i y,Nat.cast_add] at hv; rw [← Real.exp_neg,← Real.exp_neg,← Real.exp_neg,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; have hm':0 ≤ (separation y i:ℝ):= Nat.cast_nonneg _; nlinarith
variable (H:Odd S.ratio.count.val) (U: Boxes G S.patch S.kernel)(A:Clip)(W: PathData G)
variable {L:Matrix (Body 1 f) (Body 1 c) ℝ}{M:Bed}
local notation "Fλ"=> Woody.forest S.ratio H
variable {g: Bid.Dir G c→AxisChart G (Woody.forest S.ratio H)} (k:S.Choices)(h: licensed S H U A W L M g)
local notation "AK"=> Active G (forest S.ratio H)
include h
abbrev limbC (G:Gauge)(t R:ℝ):= farm G (t/2/2)*(R*Premium.overall (t/2))
lemma Palm {p:Site f→(Bid.Dir G c ×AxisChart G (forest S.ratio H))→ℝ} (ht:0<t)(hR:0≤R)(he:0<ε)(hx: Dew.Pile S (Woody.forest S.ratio H) ε R t m (pane Fλ k A W) p)(hm:2 ≤ m):
        Pours (FUND S H U) (pointK S Fλ) (pointK S Fλ) (t/2/2) (limbC G t R):=by
              refine tillS S Fλ (A:=FUND S H U) (half_pos ht) (mul_nonneg hR (zero_le_one.trans (Premium.cover_ge _))) (fun i j=>?_)
              let Z:=FUND S H U; let Ψ:=countingBasis Fλ G; let v(x:AK):= Purchase.slew S Fλ x; let a:= pointK S Fλ i; let b:=pointK S Fλ j; let w(x):= ![v i,v j] x; let x:= pane Fλ k A W; have hh:‖(0:Bid.Dir G c ×AxisChart G Fλ)‖ < ε:=by rw [norm_zero]; exact he
              have hp : Z i j=iteratedFDeriv ℝ 2 x 0 ![v i,v j]:= by
                   have hP:= Cascade.Rill.tollY S H U h k (Ψ i) (Ψ j); rw [show ![v i,v j]=![(0,Ψ i),(0,Ψ j)] from by unfold v Purchase.slew; rw [countingBasis_apply,countingBasis_apply]]; rw [hP]; have hK(i:AK) : cash (countingBasis Fλ G) (Ψ i)=Pi.single i 1:= funext fun j=>by simp [cash,Ψ,Pi.single_apply,eq_comm]
                   rw [hK,hK]; simp [Z]
              let A(u:Site f):= wt (t/2) a b; change A a* ‖Z i j‖ ≤ _; rw [hp,hx.dunk hh,_root_.sum_apply]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Green.wt_pos ..).le).trans; rw [mul_sum]; refine (sum_le_sum (g:=fun j:Site f=>R*(wt (t/2) j a)⁻¹) (fun y _=>?_)).trans ?_
              · let c:= ![(wt t a y)⁻¹,(wt t b y)⁻¹]; have hs':= hx.voice y 0 hh 2 hm ![v i,v j] c (fun l=>by
                   fin_cases l
                   · refine ⟨inv_nonneg.mpr (Green.wt_pos t a y).le,?_⟩; change On _ _ G t y (v i) (wt t a y)⁻¹; rw [Green.wt_symm t a y]; exact Purchase.allows S Fλ i ..
                   refine ⟨inv_nonneg.mpr (Green.wt_pos t b y).le,?_⟩; change On _ _ G t y (v j) (wt t b y)⁻¹; rw [Green.wt_symm t b y]; exact Purchase.allows S Fλ j ..); unfold c Radius.Polish.budget at hs'; rw [Fin.prod_univ_two] at hs'; refine (mul_le_mul_of_nonneg_left hs' (Green.wt_pos ..).le).trans ?_; change wt (t/2) a b*(R*((wt _ _ _)⁻¹*_))≤_; rw [mul_left_comm];exact mul_le_mul_of_nonneg_left (eaten a b y ht) hR
              rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (by simpa using Premium.lives 1 (half_pos ht) a) hR
end YM.OPE.Limn
