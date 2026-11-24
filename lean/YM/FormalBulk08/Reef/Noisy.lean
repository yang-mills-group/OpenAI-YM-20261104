import YM.FormalBulk08.Reef.Pines
import YM.Work.F04.Choices

/-! Exact tag germ in the step. λ here in `S.kernel.penalty`, *before*
coupling reset; prediction not merely the linear `probe`. Haar separately.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free Work.F08 Stationary Tree Wilson
open Series Jets Wick Orb PowerSeries
open scoped Topology BigOperators Matrix ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f) (hp : S.patch.Branches S.kernel G) (t r : S.Choices)

abbrev Glob (G : Gauge) (c f : Side) := wire G f ⊕ wire G c

def frail (x : Rays (Glob G c f)) : Work.F03.Logs G c f := (arm G c 1 (x ∘ Sum.inr), arm G f 1 (x ∘ Sum.inl))
def clack (x : Rays (Glob G c f)) := noiseTaylor S (represent (frail x).1) (represent (frail x).2) t
lemma frail_health : ContDiffAt ℝ ω (@frail G c f) 0 := ContDiffAt.prodMk
   ((arm G c 1).contDiff.contDiffAt.comp (f:=fun x=> x ∘ Sum.inr) _ (contDiffAt_pi.mpr fun _=> contDiffAt_apply ..))
   ((arm G f 1).contDiff.contDiffAt.comp (f:=fun x=> x ∘ Sum.inl) _ (contDiffAt_pi.mpr fun _=> contDiffAt_apply ..))
@[simp] lemma frail_zero : frail (0 : Rays (Glob G c f))=0 := by rw [frail, show _ ∘ (Sum.inr : wire G c→ _)=0 from rfl, show _ ∘ (Sum.inl : wire G f→ _)=0 from rfl,map_zero,map_zero]; rfl

def grumble (x : Rays (Glob G c f)) := x ∘ Sum.inr - patron G (Precision.probe S)*ᵥ (x ∘ Sum.inl)
def clapBill (x y : Rays (Glob G c f)) := S.kernel.penalty * dotProduct (grumble S x) (grumble S y)

private lemma paid (x : Rays (Glob G c f)) : S.kernel.penalty *
    (∑ i : Body 1 c, inner ℝ (Work.F03.residual S (frail x) i) (Work.F03.residual S (frail x) i)) = clapBill S x x := by
   have he : Work.F03.residual S (frail x) = arm G c 1 (grumble S x) := by
      unfold Work.F03.residual grumble frail; dsimp only; rw [map_sub]; congr 1
      ext ⟨p,i⟩ u; exact (congr_fun (Flat.paint_eats (probe S) (x ∘ Sum.inl) u) (p,i)).symm
   rw [he]; unfold clapBill dotProduct
   congr 1
   change (∑ i: Site c × TypeFace 1,_) = ∑ i : Site c × TypeFace 1 × G.ColorIndex,_; simp_rw [Fintype.sum_prod_type]
   apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl; intro j _
   simp only [PiLp.inner_apply]; simp_rw [RCLike.inner_apply]; rfl -- direction
include hp
lemma discord : ContDiffAt ℝ ω (@clack G c f S t) 0 := by
   have hm (i:Edge (Site c)): ContDiffAt ℝ ω (fun v : Rays (Glob G c f)=>G.mat (S.prediction (represent (frail v).2) t i)) 0 :=
       (show ContDiffAt ℝ ω (fun x=>G.mat (S.prediction (represent x) t i)) (frail 0).2 from (by simpa only [frail_zero] using! YM.Push.prediction_cont S hp i t)).comp (f:=fun v=> (frail v).2) 0 frail_health.snd
   unfold clack noiseTaylor; refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _=> ?_)
   apply Work.F03.price_smooth (A:=fun v:Rays (Glob G c f)=> represent (frail v).1 i*(S.prediction (represent (frail v).2) t i)⁻¹)
   simp_rw [G.mat_mul, G.mat_inv]; exact ContDiffAt.mul ((Work.F03.represent_smooth (G:=G) i).contDiffAt.comp (f:=fun v:Rays (Glob G c f)=> (frail v).1) 0 frail_health.fst) ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hm i))

lemma applause :
   let F := @clack G c f S t
   F 0=0 ∧ fderiv ℝ F 0=0 ∧ ∀ x y, iteratedFDeriv ℝ 2 F 0 ![x,y] = clapBill S x y := by
   intro F; apply Work.F03.hessian_of_limit ((discord _ hp t).of_le le_top)
   · intro x; obtain he := Work.F03.noise_limit hp t (frail x); rw [paid] at he; apply he.congr'; refine Eventually.of_forall fun g=>?_
     change _=clack S t _ / _
     rw [clack,show frail (g • x)=g • frail x from ?_]
     · rfl
     ext1
     · exact map_smul (arm G c 1) g _
     exact map_smul (arm G f 1) g _
   · intro u v w; unfold clapBill; rw [show grumble S (u+v)=grumble S u+grumble S v from ?_,add_dotProduct,mul_add]
     change (u ∘ Sum.inr + v ∘ Sum.inr)-patron G (Precision.probe S)*ᵥ (u∘Sum.inl+v∘Sum.inl)=_
     rw [Matrix.mulVec_add]; unfold grumble; abel
   intro u v; unfold clapBill; rw [dotProduct_comm]

def noisePin := afterX (Jets.paste (@clack G c f S t)) 2
lemma salute : X^2 * noisePin (G:=G) S t=Jets.paste (clack S t) := by
   apply after_rope; intro i hi
   obtain ⟨h,e,-⟩:=applause S hp t; interval_cases i
   · rw [paste_first,h,map_zero]
   apply orbit_ext;intro x; rw [trace_paste]; simp [PertExtension.Series.Radial.jet,e,traceP]
lemma clap_value (x:Rays (Glob G c f)): traceP x (coeff 0 (noisePin S t)) = clapBill S x x /2 := by
   rw [noisePin,after_one,Nat.add_zero,trace_paste];
   unfold PertExtension.Series.Radial.jet; rw [show (fun _ : Fin 2=> x)=![x,x] from funext fun i=>by fin_cases i <;> simp,(applause S hp t).2.2];norm_num; ring
lemma clash : noisePin (G:=G) S t=noisePin S r := by
   apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R:=_))); rw [salute S hp,salute S hp]
   apply paste_replace
   have hh : Tendsto (fun x:Rays (Glob G c f)=> (frail x).2) (𝓝 0) (𝓝 0) := by simpa only [frail_zero] using! (frail_health (G:=G) (c:=c) (f:=f)).snd.continuousAt.tendsto
   filter_upwards [eventually_all.mpr (fun i=> hh.eventually (Work.F04.prediction_germ_chart hp t r i))] with x hx; unfold clack noiseTaylor
   rw [funext hx]
lemma clamor : ∀ᶠ U:Config G f in 𝓝 1, ∀ (g : ℝ) (V : Config G c), S.density g U V=S.noise g (S.prediction U t) V := by
   filter_upwards [eventually_all.mpr (fun i=>Work.F04.prediction_germ hp i t)] with U h g V; unfold StepData.density
   simp_rw [show ∀ i,S.prediction U i=S.prediction U t from h,← Finset.sum_mul,S.chosen hp,one_mul]
end YM.FormalBulk08.Reef
