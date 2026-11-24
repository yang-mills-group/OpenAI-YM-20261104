import YM.MSbar.Kelvin.Mercy
import YM.MSbar.Kelvin.Mead
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar MvPolynomial Analysis Bakery Lattice
variable {ι σ τ: Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {F : Cacao.View σ→ℝ}{k: Matrix ι ι ℝ} (V:Matrix σ ι ℝ)(μ:View σ)
set_option quotPrecheck false
local notation "H"=> View ι
local notation "P"=> Pot σ
local notation "Z"=> View σ
local notation "ϑ"=> fieldLaw k
variable (h:k.PosDef)
def pen (μ:View σ) (V: Matrix σ ι ℝ): View ι → View σ :=fun v=> μ + V *ᵥ v
def hint (μ:View σ) (V :Matrix σ ι ℝ)(k:Matrix ι ι ℝ)(f : View σ→ℝ)(Pp:Pot σ): ℝ:=
    (∫ i, f (pen μ V i) * MvPolynomial.eval (pen μ V i) Pp∂fieldLaw k) -
    (∫ i,f (pen μ V i) ∂fieldLaw k)*(∫ i, MvPolynomial.eval (pen μ V i) Pp∂fieldLaw k)
-- Frame.Bounded just finite.Cut.No uniform constant.
structure Canopy (F: View σ→ℝ) :Prop where
   light : ContDiff ℝ 1 F
   whole : ∃ c:ℝ,∀ y, |F y|≤ c
   chart j : ∃ t,∀ i,|glance F [j] i| ≤ t
variable (e:Canopy F)
local notation "δ"=> pen μ V
local notation "k!"=> V*k*V.transpose
local notation "r!"=> hint μ V k
noncomputable def pillar (j:σ) (F: View σ→ℝ) (Pp:Pot σ)(k:Matrix ι ι ℝ) := ∫ i, glance F [j] (pen μ V i)* MvPolynomial.eval (pen μ V i) Pp∂ fieldLaw k
include h
lemma paidHelp (p:Pot σ) (f:View σ→ℝ)(hf:Continuous f) (H':∃ c:ℝ,∀ x, |f x| ≤ c) : Integrable (fun i=> f (pen μ V i)*MvPolynomial.eval (pen μ V i) p) (fieldLaw k):=by
    let w:= δ; have hh:Continuous w:=by unfold w pen; exact continuous_const.add (toLin' V).continuous_of_finiteDimensional
    have hp:=grille V h p μ 1 (by norm_num); obtain ⟨c,hc⟩:= H'; let A(i):=MvPolynomial.eval (w i) p
    refine (hp.integrable (le_refl _) |>.norm.const_mul c).mono' (((hf.comp hh).mul ((vent p).continuous.comp hh)).aestronglyMeasurable) ?_; refine ae_of_all _ fun v=> ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc (w v)) (norm_nonneg _)
omit h in
lemma curtain (i:σ) (e: Canopy F): Continuous (glance F [i]) :=by
    apply continuous_iff_continuousAt.mpr; intro v; apply (glow (n:=0) [i] (d:=1) (by norm_num; exact e.light.contDiffAt) (by simp)).continuousAt
lemma teal (i:σ) (q:Pot σ): V*ᵥ Cacao.dir_G i V k = fun j=> (k!) i j:=traces V h _ (0:View ι)
include e
lemma pint : ∃ f: P →ₗ[ℝ]ℝ, ∀ p:Pot σ,f p = hint μ V k F p :=by
    have hv(p:P):= paidHelp V μ h p F e.light.continuous e.whole
    have hh(p:P) : Integrable (fun t=>eval (pen μ V t) p) (fieldLaw k):= (grille V h p μ 1 (by norm_num)|>.integrable (le_refl _)); let g':P →ₗ[ℝ]ℝ:= {
       toFun:= hint μ V k F
       map_add' p q:=by unfold hint; simp_rw [_root_.map_add,mul_add]; rw [integral_add (hv p) (hv q),integral_add (show Integrable _ _ from hh p) (hh q)]; ring
       map_smul' r p:=by unfold hint; simp_rw [← C_mul',_root_.map_mul,MvPolynomial.eval_C,mul_left_comm (F _) r, integral_const_mul]; simp only [RingHom.id_apply,smul_eq_mul];ring }
    exact ⟨g',fun i=>rfl⟩
lemma atop (p:P)(i:σ): r! F (p* MvPolynomial.X i)= r! F p *μ i+r! F ((tureen (k!) i) p)+ ∑ j:σ, (k!) i j * pillar V μ j F p k :=by
    let q(r:H):= MvPolynomial.eval (pen μ V r) p; let T:= Cacao.tureen (V*k*V.transpose) i p; let h₀(Y):= F (δ Y); let T'(Y:H):= MvPolynomial.eval (pen μ V Y) T; let D(j:σ)(x):=glance F [j] (δ x)
    let W(y):= h₀ y*q y; let d(y):= (∑ j:σ,(V*k*V.transpose) i j*(D j y*q y)) + h₀ y * T' y; let v:=dir_G i V k; let m:= fieldLaw k
    have hm:Continuous (δ):=continuous_const.add (toLin' V).continuous_of_finiteDimensional
    have hh:Continuous W:=(e.light.continuous.comp hm).mul ((vent p).continuous.comp hm); have hd: Continuous d:=by
       refine Continuous.add (continuous_finsetSum _ (fun j _=>Continuous.mul continuous_const ?_)) ((e.light.continuous.comp hm).mul ((vent T).continuous.comp hm)); exact Continuous.mul ((curtain j e).comp hm) ((vent p).continuous.comp hm)
    have hc(p:P):= paidHelp V μ h p F e.light.continuous e.whole; have he(j:σ): Integrable (fun y=> (V*k*V.transpose) i j*(D j y*q y)) m:= (paidHelp V μ h p (glance F [j]) (curtain j e) (e.chart j)).const_mul _
    have hp(y:H): HasDerivAt (fun t:ℝ=> W (y+t•v)) (d y) 0 := by
       have hh: HasDerivAt (fun t:ℝ=> h₀ (y+t • v)) (∑ j,(V*k*V.transpose) i j*D j y) 0:=by
           let f:=pen μ V; let G:= V*ᵥ v; have hx:∀ a:ℝ, pen μ V (y+a•v)= pen μ V y + a • (V*ᵥ v):=by intro a; unfold pen; rw [Matrix.mulVec_add,Matrix.mulVec_smul,← add_assoc]
           have hh:V *ᵥ v=fun j=> (V*k*V.transpose) i j:=traces V h i y; unfold h₀; simp_rw [hx]; have hP:=e.light.differentiable (by norm_num); have hk:= Bakery.lamp (f:=F) (x:=pen μ V y) (y:=V*ᵥ v) (0:ℝ) (hP.differentiableAt); simp only [zero_smul,add_zero] at hk
           apply (show HasDerivAt _ _ _ from hk).congr_deriv; rw [hh]; rfl -- lemma name
       have hx:= hh.mul (twigs V h μ p i y); simp only [zero_smul,add_zero] at hx; refine hx.congr_deriv ?_; unfold d D q h₀ T' T; dsimp only [pen]; rw [Finset.sum_mul]; congr 1; apply sum_congr rfl; intro j _; exact mul_assoc _ _ _ 
    let X(i':H):= F (δ i') * (MvPolynomial.eval (δ i')) (p * MvPolynomial.X i); have hx(y): dotProduct (k⁻¹*ᵥy) v * W y = X y-W y*μ i:=by
       rw [terrace V h μ i]; unfold X W h₀ q; unfold pen; simp only [map_mul,eval_X]; ring
    have hW := steamed h v hh hd (show Integrable W ϑ from hc p) (show Integrable d ϑ from ((integrable_finsetSum Finset.univ (fun j _=>he j)).add (hc T))) (show Integrable _ ϑ from (by simp_rw [hx]; exact (hc (p*MvPolynomial.X i)).sub ((hc p).mul_const _))) hp
    rw [show (∫ y,d y∂ϑ)=(∑ j,(V*k*V.transpose) i j * pillar V μ j F p k)+(∫ y,h₀ y*T' y∂ϑ) from ?_] at hW; swap; · unfold d; rw [MeasureTheory.integral_add (integrable_finsetSum _ (fun j _=>he j)) (show Integrable (fun i'=> h₀ i' *T' i') _ from hc T),integral_finsetSum _ (fun j _=>he j)]; simp only [integral_const_mul]; rfl
    simp_rw [hx,MeasureTheory.integral_sub (show Integrable X ϑ from hc _) ((show Integrable W ϑ from hc p).mul_const _),MeasureTheory.integral_mul_const] at hW
    unfold hint; rw [show (∫ z,MvPolynomial.eval (pen μ V z) (p* MvPolynomial.X i)∂ϑ) = (∫ z,MvPolynomial.eval (pen μ V z) p ∂ϑ)*μ i+(∫ z,MvPolynomial.eval (pen μ V z) T∂ϑ) from peas V h μ p i]
    let z:=∫ z:View ι,h₀ z∂ ϑ; change (∫ z,X z ∂ϑ)-z*((∫ z,q z∂ϑ)*_+(∫ z,T' z∂ϑ))=((∫ y,W y∂ϑ)-z* _)*μ i+((∫ z,h₀ z*T' z∂ϑ)-z*_)+_; rw [show (∫ z,X z∂ϑ)= (∑ j,(V*k*V.transpose) i j * pillar V μ j F p k)+(∫ y,h₀ y*T' y∂ϑ)+(∫ z,W z∂ϑ)*μ i from eq_add_of_sub_eq hW.symm]; unfold q T' T; ring
end YM.MSbar.Kelvin
