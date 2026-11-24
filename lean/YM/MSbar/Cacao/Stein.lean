import YM.MSbar.Cacao.Stock
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open MeasureTheory Filter Function Finset Matrix
open ProbabilityTheory MvPolynomial
open scoped Topology BigOperators Classical
variable {σ : Type}[Fintype σ][DecidableEq σ]
open Further.GaussianScalar
abbrev View (σ:Type) := (σ →ℝ)
local notation "H"=> View σ
local notation "P"=> Pot σ
variable {g : Matrix σ σ ℝ} {f df : View σ→ℝ}
-- line.Diff sufficient. Joint at any x.Support all.E.One dimension fundamental interval.
omit [DecidableEq σ] in
lemma slice_shift (μ:Measure H) [SigmaFinite μ][μ.IsAddHaarMeasure] (v:H)(hp:Continuous df) (hi: Integrable f μ) (hv:Integrable df μ)(h :∀ x:H, HasDerivAt (fun t:ℝ=> f (x+t • v)) (df x) 0) : (∫ x,df x∂ μ)=0:=by
    let I:= Set.Ioc (0:ℝ) 1; let m:Measure ℝ:= volume.restrict I; haveI :IsFiniteMeasure m:=by unfold m I;infer_instance
    let q(x:H)(t:ℝ):=f (x+t • v); let y(x:H)(t:ℝ):=df (x+t • v); let a(u:ℝ×H):= y u.2 u.1
    have he : Continuous a:=by unfold a y; fun_prop
    have hb : Integrable a (m.prod μ) := by
       apply (MeasureTheory.integrable_prod_iff he.aestronglyMeasurable).2
       have hx(z):MeasurePreserving (· + z:H→H) μ μ:=measurePreserving_add_right μ z; constructor
       · exact Eventually.of_forall (fun t=> ((hx (t • v)).integrable_comp_emb ((Homeomorph.addRight _).measurableEmbedding)).mpr hv)
       unfold a y; have he (t:ℝ): (∫ x:H,‖df (x+t•v)‖∂μ)= ∫ x:H,‖df x‖∂μ:=by simpa using (hx (t • v)).integral_comp ((Homeomorph.addRight _).measurableEmbedding) (fun x=>‖df x‖)
       dsimp only; simp_rw [he]; exact integrable_const _
    have hD(x:H)(t:ℝ): HasDerivAt (q x) (y x t) t:=by
       let f'(r :ℝ):= f ((x+t • v)+r • v); have he: HasDerivAt (fun r:ℝ=> r-t) 1 t:= (hasDerivAt_id' _).sub_const t
       have hx := (show HasDerivAt f' (df (x+t • v)) ((fun r=> r-t) t) from (by dsimp only;rw [sub_self]; exact h _)).comp (h:=(fun r=> r-t)) t he
       rw [show f' ∘ (fun r=> r-t)=q x from funext (fun r=>by unfold f' q Function.comp; dsimp only; rw [sub_smul,add_assoc]; congr 1; abel),mul_one] at hx; exact hx
    have hc(x:H): (∫ t, a (t,x) ∂m)=f (x+v)-f x := by
       change (∫ t in I,y x t) = _; rw [← intervalIntegral.integral_of_le (show (0:ℝ)≤1 from zero_le_one)]
       suffices h:(∫ t in (0:ℝ)..1,y x t)=q x 1 - q x 0 by simpa [q] using h
       exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hD x t) ((show Continuous (y x) from he.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    have heq(t:ℝ): (∫ x:H,a (t,x)∂ μ)= (∫ x, df x∂ μ):=(measurePreserving_add_right μ (t • v)).integral_comp ((Homeomorph.addRight _).measurableEmbedding) df
    have hw : m.real Set.univ=1:=by unfold m I; simp [measureReal_def]
    have hp := measurePreserving_add_right μ v; calc
       _ = ∫ y,∫ x,a (y,x)∂μ∂ m:= by simp_rw [heq]; rw [integral_const,hw,one_smul]
       _ = ∫ x,∫ y,a (y,x)∂m∂ μ:=integral_integral_swap hb
       _ = _ := by simp_rw [hc]; rw [integral_sub (show Integrable (fun x=> f (x+v)) μ from (((hp.integrable_comp_emb (Homeomorph.addRight v).measurableEmbedding)).mpr hi)) hi,show (∫ x,f (x+v)∂μ)= ∫ x,f x∂μ from hp.integral_comp ((Homeomorph.addRight v).measurableEmbedding) f, sub_self]
-- integration along column.K.Op.
lemma powerLine (h:g.PosDef)(b:H)(x:H) : HasDerivAt (fun z:ℝ=> lawPDF g (x+z • b)) (-(dotProduct (g⁻¹ *ᵥ x) b)*lawPDF g x) 0 :=by
   let f(t:ℝ):= x+t • b; let v:= f; let G:= g⁻¹; let A(t:ℝ):= dotProduct (f t) (G *ᵥ f t); let Y:= dotProduct (G *ᵥ x) b; let B:= lawPDF g
   have hy:dotProduct x (G *ᵥ b)= Y:= by rw [dotProduct_mulVec,← mulVec_transpose]; rw [show G.transpose=G from (by simpa [Matrix.IsHermitian] using h.inv.1)]; -- defeq
   have he(t:ℝ): A t = dotProduct x (G *ᵥ x)+ t*(2*Y)+t^2*dotProduct b (G *ᵥ b):=by
      unfold A f; simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_smul,smul_dotProduct, smul_eq_mul]; rw [hy,dotProduct_comm b]; unfold Y; ring
   have h0 : A 0= dotProduct x (G *ᵥ x):=by rw [he]; ring
   have ht : HasDerivAt A (2*Y) 0:=by
       rw [funext he]; let z:= dotProduct b (G *ᵥ b); let k:=dotProduct x (G *ᵥ x); simpa using! ((((hasDerivAt_id' 0).mul_const (2*Y)).const_add k).add (((hasDerivAt_id' 0).pow 2).mul_const z))
   have hh:= (((ht.neg.div_const 2).exp).const_mul (modeCost g)⁻¹); convert! hh using 1; unfold lawPDF; rw [Pi.neg_apply,h0]; unfold Y; unfold G at *; ring
lemma steamed (h:g.PosDef)(v:H)(he:Continuous f)(hd:Continuous df)(hb: Integrable f (fieldLaw g))(hi:Integrable df (fieldLaw g))
    (hs: Integrable (fun x:H=> (dotProduct (g⁻¹ *ᵥ x) v) *f x) (fieldLaw g)) (hp: ∀ x:H, HasDerivAt (fun u:ℝ=> f (x+u • v)) (df x) 0):
      (∫ x,df x ∂fieldLaw g)=(∫ x, (dotProduct (g⁻¹ *ᵥ x) v)*f x ∂fieldLaw g):=by
   let a:= lawPDF g; let k(t:H):=dotProduct (g⁻¹ *ᵥ t) v*f t; let G(x:H):= a x * (df x-k x)
   suffices hh : (∫ x,G x)=0 by
       apply sub_eq_zero.mp; rw [← integral_sub hi hs, show (∫ x, (df x-k x)∂fieldLaw g)=(∫ x,G x) from integral_law h _,hh]
   have hv:Continuous a:= lawPDF_cont _; let u(x:H):= a x*f x
   refine slice_shift (volume (α:=H)) (f:=u) v ?_ ((integrable_law h f).1 hb) ((integrable_law h (df-k)).1 (hi.sub hs)) (fun x=>?_)
   · unfold G k; have ht : Continuous fun x:H=>g⁻¹*ᵥx := (toLin' g⁻¹).continuous_of_finiteDimensional; apply Continuous.mul hv (hd.sub ?_); apply Continuous.mul _ he; exact (show Continuous (fun j:H=> dotProduct j v) by unfold dotProduct; fun_prop).comp ht
   have h:= (powerLine h v x).mul (hp x); simp only [zero_smul,add_zero] at h; convert! h using 1; unfold G a k; ring
end YM.MSbar.Cacao
