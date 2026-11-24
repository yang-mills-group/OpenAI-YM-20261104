import YM.AllOrder.Floe.Circle
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
namespace Crest
/-! Choose curvature book through all orders *before* L restriction. Takes peak.T.Purchase implied basis via canon. Keep regulator link unmasked & Symm actions. -/
open WilsonStartup WilsonStartup.Design WilsonStartup.Padded Work Tensor
variable (p:Clip)
open StateE Pace
abbrev picture(m:ℕ)(U:Config G n):= mainTerm p (Design.top G p) U+scene p m U
def margin(m:ℕ)(U:Config G n):= bulk p * ∑ b:WilsonStartup.Cell n, short m (faceValue U b)
lemma funds (m:ℕ)(U:Config G n)(h:p.direct≤1): energy U=picture p m U+margin p m U:= by unfold picture margin; rw [site, main_top p U h]; simp only [Design.diff,WilsonStartup.residual, short, Finset.sum_sub_distrib, ← mul_sum]; ring
lemma elation (m:ℕ)(g:ℝ): audition (f:=n) (Design.top G p) p (tile p G) (Age.scope (m+2)) g = picture (G:=G) p m:= by ext1 U; unfold audition; simp only [Finset.sum_apply,Pi.add_apply, Laplace.primitive, no_loop,mul_zero,add_zero, gridV]
local notation "Y"=> Stationary.Link G n
local notation "L"=>Stationary.input G n
lemma summed {ι:Type}(s:Finset ι)(f:ι→Y→ℝ)(h:∀ i∈s,ContDiffAt ℝ ω (f i) 0)(k:ℕ)(x:Y): jet (∑ i∈s,f i) k x=∑ i∈s,jet (f i) k x := by
 rw [jet, iteratedFDeriv_sum_apply (fun i hi=> (h i hi).of_le le_top), _root_.sum_apply] -- name.TBD
 simp_rw [mul_sum]; rfl
lemma witness (b:WilsonStartup.Cell n) : ContDiffAt ℝ ω (fun x:Y=> G.mat (faceValue (L x) b)) 0:= by
 simp only [← read_edges, ← Quad.read_actual]; refine Quad.readMat_diff.contDiffAt.comp _ (contDiffAt_pi.mpr fun i=>?_); exact ((F03.represent_smooth _).comp (arm G n 1).contDiff).contDiffAt
lemma base_pose' (hp:p.direct≤1) (x:Y) : ContDiffAt ℝ ω (mainTerm p (Design.top G p) ∘ L) 0 := by obtain ⟨b,h,hc⟩:=bound_arbitrary p G hp 1 zero_lt_one; exact (Pace.intent_point p _ (hc b le_rfl 0 le_rfl) n|>.analytic).contDiffAt -- hc names
lemma smoothV(n:Side)(m:ℕ)(hp:p.direct≤1): ContDiffAt ℝ ω (picture (G:=G) (n:=n) p m ∘ Stationary.input G n) 0:= by
 let f(i:Age):=turnSeries (m:=n) (tile p G i); exact ContDiffAt.add (base_pose' p hp 0) (ContDiffAt.sum fun i h'=> (turns_analytic _ zero_lt_one (info p G i 1|>.pay) (m:=n)).contDiffAt) -- n fresh implicit inference
lemma margin_value(n:Side)(m:ℕ) : ContDiffAt ℝ ω (margin p m ∘ Stationary.input G n) 0 ∧ FlatAt (m+5) (margin p m ∘ Stationary.input G n) 0 := by -- implicit G cannot infer need (G:=G)
 let f(b:WilsonStartup.Cell n) (x:Stationary.Link G n):= short m (faceValue (Stationary.input G n x) b); let F:=∑ b, f b; have hf b:ContDiffAt ℝ ω (f b) 0:= by simp_rw [f,← PhaseK.ambient_actual]; exact PhaseK.diff _|>.contDiffAt.comp _ (witness ..)
 have hF : ContDiffAt ℝ ω F 0:= by rw [show F= _ from (show F=(fun x=>∑ b,f b x) from funext fun _=> Finset.sum_apply ..)]; exact ContDiffAt.sum fun b _ => hf b
 have he : margin p m ∘ Stationary.input G n=bulk p • F:= funext fun u=> congr_arg (bulk p*·) (Finset.sum_apply u univ f).symm
 rw [he]; refine ⟨hF.const_smul (bulk p),?_⟩
 intro i hi; rw [iteratedFDeriv_const_smul_apply (hF.of_le le_top)]; unfold F; rw [iteratedFDeriv_sum_apply (fun b _=>(hf b).of_le le_top),Finset.sum_eq_zero (fun b _=>show iteratedFDeriv ℝ i (f b) 0=0 from collation (G:=G) (fun x=> faceValue (Stationary.input G n x) b) (by rw [input_zero]; exact face_one b) (witness b) m i hi),smul_zero]
/-! The literal bare uncut Wilson action germ (not read from PT detector). -/
theorem summit (k:ℕ)(h:p.direct≤1) {j:ℕ}(hj:j≤k+2)(n:Side): Pace.grouping 0 (tile p G) (Age.scope (k+2)) p (Design.top G p) j n=jet (energy ∘ Stationary.input G n) (j+2):= by
 let F:=picture (n:=n) (G:=G) p k; let W :=Stationary.input G n; let V:=F ∘ W; let R₀:=Age.scope (k+2); let f(i:Age):=turnSeries (tile p G i) (m:=n); let M:=∑ i∈R₀,f i
 have he : V=(mainTerm p (Design.top G p) ∘ W) +M:= funext fun y =>congr_arg _ (show scene p k (W y)=M y from (Finset.sum_apply y R₀ f).symm);
 have ht : ContDiffAt ℝ ω M 0:= by rw [show M= _ from (show M=(fun x=>∑ b∈R₀,f b x) from funext fun _=> Finset.sum_apply ..)]; exact ContDiffAt.sum fun i h'=> (turns_analytic _ zero_lt_one (info p G i 1|>.pay)).contDiffAt
 obtain ⟨hm,hM⟩:= margin_value (G:=G) p n k; unfold grouping shiftB; simp only [Pi.add_apply, nogo, add_zero];
 rw [show Wilson.energy ∘ Stationary.input G n= V+margin p k ∘ W from funext fun a=> funds p k (W a) h];
 have hp : Coat.clerk (fun _=> Precision.loop (Design.top G p)) 0 j n=0:= by unfold Coat.clerk; rw [show Precision.loop _ ∘ Stationary.input G n= (0:Stationary.Link G n→ℝ) from funext fun u=> no_loop p (W u)]; ext; simp [jet]
 rw [hp,add_zero]; funext x;
 rw [jet_add (smoothV p n k h) hm]; rw [show jet (margin p k ∘ W) (j+2) x=0 by unfold jet; rw [hM (j+2) (by omega)]; simp,add_zero];
 change _=jet V (j+2) x; rw [he,jet_add (base_pose' p h x) ht]; simp only [Pi.add_apply,glory,Finset.sum_apply,gridN]; exact congr_arg (jet (mainTerm p (Design.top G p) ∘ W) (j+2) x + ·) (summed R₀ f (fun i hi=>(turns_analytic _ zero_lt_one (info p G i 1|>.pay)).contDiffAt) _ x).symm
end Crest
end YM.AllOrder.Floe
