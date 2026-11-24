import YM.MSbar.Rolling.Thermal
import YM.Work.F03
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push Push.Uniform Exterior
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
open Work.F03
-- genuine real Haar densities expo sign accounted later. native.J
local notation "∆"=> fderiv ℝ
def Premier {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E] (f:E→ℝ):= ContDiffAt ℝ ω f 0 ∧ f 0=0∧ fderiv ℝ f 0=0
namespace Premier
variable {g:E→ℝ} (h : Premier g){w:F→E} (hx:ContDiffAt ℝ ω w 0)(hp:w 0=0)
lemma congrR {z':E→ℝ} (he:g =ᶠ[𝓝 0] (fun z:E => z' z))(hz:Premier g):Premier z':= by -- autoImplicit false.rm
    exact ⟨hz.1.congr_of_eventuallyEq he.symm,he.eq_of_nhds.symm.trans hz.2.1,he.fderiv_eq.symm.trans hz.2.2⟩
include h
lemma second (x:E) : Tensor.diagonal (Tensor.coeff g 2 0) x= (1/2)*rim g x x:=by unfold Tensor.diagonal Tensor.coeff; simp only [_root_.smul_apply,iteratedFDeriv_two_apply,smul_eq_mul]; norm_num [rim]
lemma zeroP (k:ℕ) (x:E)(he:k<2):Tensor.diagonal (Tensor.coeff g k 0) x=0:=by interval_cases k; exact (Tensor.coeff_apply_zero ..).trans h.2.1; unfold Tensor.diagonal Tensor.coeff; simp only [_root_.smul_apply,iteratedFDeriv_one_apply,h.2.2]; simp
lemma negp : Premier (fun x=> -(g x)):=by refine ⟨h.1.neg,by dsimp only; rw [h.2.1,neg_zero],?_⟩; change ∆ (-g) 0=0; rw [fderiv_neg,h.2.2,neg_zero]
lemma pair {g':E→ ℝ}(hp:Premier g') : Premier (fun x=>g x+g' x):=by
   refine ⟨h.1.add hp.1,by dsimp only; rw [h.2.1,hp.2.1,add_zero],?_⟩; change ∆ (g+g') 0=0; rw [fderiv_add (h.1.differentiableAt (by simp)) (hp.1.differentiableAt (by simp)), h.2.2,hp.2.2,add_zero]
lemma stitch {g':E→ℝ}(he:∀ j≤1,SameJet j g g') : Premier g':=by
    refine ⟨(he 1 le_rfl).2.1,?_,?_⟩
    · have h0 := congr_arg (fun f:Tensor.T E ℝ 0=>f (fun _ : Fin 0=>0)) ((he 0 (by omega)).2.2); change iteratedFDeriv ℝ 0 _ 0 _=iteratedFDeriv ℝ 0 _ 0 _ at h0; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply] at h0; exact h0.symm.trans h.2.1
    ext1 x; have hx := congr_arg (fun f:Tensor.T E ℝ 1=>f ![x]) ((he 1 le_rfl).2.2); change iteratedFDeriv ℝ 1 _ 0 _=iteratedFDeriv ℝ 1 _ 0 _ at hx; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,h.2.2] at hx; exact hx.symm
lemma line (L:F →L[ℝ] E): Premier (g ∘ L) := by
    refine ⟨ (show ContDiffAt ℝ ω g (L 0) from by rw [map_zero]; exact h.1).comp _ L.contDiff.contDiffAt, by rw [Function.comp_apply,map_zero,h.2.1],?_⟩; rw [fderiv_comp _ (by rw [map_zero]; exact h.1.differentiableAt (by simp)) L.differentiableAt,L.fderiv,map_zero,h.2.2]; simp
include hp hx
lemma make : Premier (g ∘ w):= ⟨ (hp.symm ▸ h.1:ContDiffAt ℝ ω g (w 0)).comp _ hx, by rw [Function.comp_apply,hp,h.2.1],(hessian_comp hp (h.1.of_le le_top) (hx.of_le le_top) h.2.2).1⟩
lemma station(x:F)(y:F) : rim (g ∘ w) x y=rim g ((∆ w 0) x) ((∆ w 0) y) := by have hz:=(hessian_comp hp (h.1.of_le le_top) (hx.of_le le_top) h.2.2).2 x y; simp only [iteratedFDeriv_two_apply] at hz; exact hz
omit hx hp
lemma carriage (L:F→L[ℝ] E)(x y:F) : rim (g ∘ L) x y = rim g (L x) (L y):=by have he:= h.station L.contDiff.contDiffAt (map_zero L) x y; rwa [L.fderiv] at he
lemma joined {g':E→ℝ}(h':Premier g')(x y:E) : rim (g+g') x y=rim g x y+rim g' x y:=by
    have hh := congr_arg (fun i:Tensor.T E ℝ 2=>i ![x,y]) (iteratedFDeriv_add_apply (𝕜:=ℝ) (h.1.of_le (m:=↑(2:ℕ)) le_top) (h'.1.of_le le_top)); change iteratedFDeriv ℝ _ _ _ _=_ at hh; simp only [_root_.add_apply,iteratedFDeriv_two_apply] at hh; exact hh
end Premier
variable {c f:Side}{S:StepData c f}
variable (B: Forest S.ratio)(t:S.Choices)(p:Clip)(R:PathData G)
local notation "V"=>fieldDir G c 1
local notation "W"=>fieldDir G f 1
local notation "i!"=>Logs G c f
variable (h:S.patch.Branches S.kernel G)
def main (c : Side) (p:Clip)(R : PathData G)(x:fieldDir G c 1):= mainTerm p R (represent x)
abbrev Costree (S:StepData c f)(G:Gauge)(t:S.Choices) (z:Logs G c f) := noiseTaylor S (represent z.1) (represent z.2) t
variable (g:Premier (main f p R))
include h
lemma bornCosts : Premier (Costree S G t):=by
    let F:=Costree S G t
    have hv (e : Edge (Site c)): ContDiffAt ℝ ω (fun z : i!=> G.mat (S.prediction (represent z.2) t e)) 0 :=(prediction_cont S h e t).comp (f:= Prod.snd) (0:i!) contDiffAt_snd
    have he: ContDiffAt ℝ ω F 0 := by
        unfold F Costree noiseTaylor; apply ContDiffAt.mul contDiffAt_const (ContDiffAt.sum (fun i _=> price_smooth (A:=fun z:i!=>represent z.1 i*(S.prediction (represent z.2) t i)⁻¹) ?_ )); simp only [G.mat_mul,G.mat_inv]; exact ((represent_smooth (G:=G) _).contDiffAt.comp (f:=Prod.fst) (0:i!) contDiffAt_fst).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hv i))
    have hp(z:i!) : F 0=0 ∧ HasDerivAt (fun t:ℝ=>F (t•z)) 0 0:=by
        let f(t:ℝ):=t•z; have hF: ContinuousAt f 0:=(show Continuous f from by unfold f; fun_prop).continuousAt; have hT:F (f 0)=F 0:=by unfold f; rw [zero_smul]
        have hh: ContinuousAt F (f 0):= (by unfold f; rw [zero_smul]; exact he.continuousAt)
        have hV := value_slope_of_sq_limit (hh.comp hF) (noise_limit h t z); exact ⟨hT.symm.trans hV.1,hV.2⟩ -- Lean semicolon
    exact ⟨he,(hp 0).1, ContinuousLinearMap.ext fun x => (Push.side F (he.differentiableAt (by simp)) x).unique (hp x).2⟩
include g
lemma bronze : Premier (flat S t p R) := (g.line (ContinuousLinearMap.snd ℝ V W)).pair (bornCosts t h) -- S implicit?
lemma legP : Premier (uncurry (tested B t p R)) := Premier.congrR (from_flat B t R p).symm ((bronze t p R h g).make (inclusion_smooth B) (inclusion_zero B))
lemma paysCore : Premier (priced B t p R) := (legP B t p R h g).line (paint B G).toContinuousLinearMap
lemma hessianP(x y:Work.F03.ChartVars B G) : rim (uncurry (tested B t p R)) x y = rim (flat S t p R) (x.1,Bid.stretch B x) (y.1,Bid.stretch B y):=by
    have hh:= congr_arg (fun f:Tensor.T (Work.F03.ChartVars B G) ℝ 2=>f ![x,y]) (((from_flat B t R p).iteratedFDeriv ℝ 2).eq_of_nhds); change iteratedFDeriv ℝ _ _ _ _=iteratedFDeriv ℝ _ (flat S t p R ∘ inclusion B) 0 _ at hh; simp only [iteratedFDeriv_two_apply] at hh; rw [← inclusion_deriv B x, ← inclusion_deriv B y]; exact hh.trans ((bronze t p R h g).station (inclusion_smooth B) (inclusion_zero B) _ _) -- lean rewrite orientation
end YM.MSbar.Rolling
