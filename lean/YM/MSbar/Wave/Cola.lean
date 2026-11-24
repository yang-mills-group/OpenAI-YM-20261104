import YM.MSbar.Wave.Social
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open Set MvPolynomial Analysis AnalyticBridge.VerifiedReset
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> Positions (Primary n G)
local notation "V"=> Directions G n
local notation "ϑ"=> fieldDir G n 1
-- Symmetry on the zero Hessian for PT and real boxes.
noncomputable abbrev primary (s:Edge (Site n))(i:G.ColorIndex): Primary n G:= ((s.1,Exterior.coord s.2),i)
def bead (G:Gauge)(e:Edge (Site n)) : G.Color→L[ℝ]Positions (Primary n G) := (panel G n).symm.toContinuousLinearMap.comp ((LinearMap.single ℝ (fun _ => G.Color) e).toContinuousLinearMap)
lemma edges (G:Gauge)(e:Edge (Site n))(z:G.Color): panel G n (bead G e z)=Pi.single e z:= (panel G n).apply_symm_apply _
lemma allStyle {f':X→ℝ} (k:X →L[ℝ] X) (e:f'∘ k =ᶠ[𝓝 0] f') (hp:DifferentiableAt ℝ f' 0)(x:X) : fderiv ℝ f' 0 (k x)= fderiv ℝ f' 0 x:=by
    have hh:= e.fderiv_eq (𝕜:=ℝ); rw [fderiv_comp _ (by rw [map_zero]; exact hp) k.differentiableAt, map_zero,k.fderiv] at hh; exact congr_arg (fun i:X→L[ℝ]ℝ=> i x) hh
-- bead.B(-).Need calculate direct.P.
lemma shadeK(k:G.El)(s:Edge (Site n)) (x:G.Color) : bead G s (G.adjoint k x)=hue k (bead G s x):=by
    apply (panel G n).injective; have hx(v:X):panel G n (hue k v)=colorMove k (panel G n v):= (panel G n).apply_symm_apply _
    rw [hx,edges,edges]; funext j; change Pi.single (M:=fun _:Edge (Site n)=> G.Color) s (G.adjoint k x) j=G.adjoint k (Pi.single (M:=fun _:Edge (Site n)=> G.Color) s x j); by_cases hr:j=s<;>simp only [Pi.single_apply,hr] <;> simp
lemma zero_hit {f': Positions (Primary n G)→ℝ}(hp:ContDiffAt ℝ 2 f' 0) (hG:G.Simple)(h:∀ k:G.El,f' ∘ hue k=ᶠ[𝓝 0] f') : fderiv ℝ f' 0=0 := by
    let L:= fderiv ℝ f' 0; have hv(k:G.El)(x): L (hue k x)= L x:= allStyle (hue k) (h k) (hp.differentiableAt (by simp)) x; have he(b:Edge (Site n))(x:G.Color):L (bead G b x)=0:=by
        let K:=L.toLinearMap.comp (bead G b).toLinearMap; have ht:=StressFlux.linear_invariant hG K (fun k x=>by change L (bead G b (G.adjoint k x))=_; rw [shadeK,hv];rfl); exact congr_arg (fun i:G.Color→ₗ[ℝ] ℝ=>i x) ht
    ext v; let W:=panel G n v; change L v= (0:ℝ); suffices h:v=∑ e : Edge (Site n), bead G e (W e) by nth_rw 1 [h,map_sum]; simp [he]
    apply (panel G n).injective; rw [map_sum]; simp_rw [edges]; funext e; change _= (∑ i: Edge (Site n),(Pi.single i (W i):Directions G n)) e; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem e (Finset.mem_univ _)]; · simp [W]
    intro i hi he; simp [Pi.single_apply, Ne.symm he,he]
lemma classR {F:X → ℝ}{L:X→L[ℝ] X} (h:F ∘ L=ᶠ[𝓝 0] F) (hf :ContDiffAt ℝ 2 F 0)(hp:fderiv ℝ F 0=0) (x y:X) : rim F (L x) (L y)=rim F x y:=by
   have he:= Work.F03.hessian_comp L.map_zero hf L.contDiff.contDiffAt hp|>.2 x y; rw [(h.iteratedFDeriv ℝ 2).eq_of_nhds, L.fderiv, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply] at he; exact he.symm
-- T direction gradient.
lemma billFlight (f:PowerSeries (Cacao.Pot (Primary n G))) (p i:ℕ)(z:Site n→ G.Color)(x:Positions (Primary n G)) : bill (flight f p z x) i = impulse n G (µ p f) x (Tensor.diagonal (Tensor.coeff (speedsK z) i 0) x):=by
    let A:= impulse n G (µ p f) x; let K(v) := speedsK z v
    have hk : ContDiffAt ℝ ω K 0:=by
        let F:= (tint G (Body 1 n)).symm; apply F.contDiff.contDiffAt.comp; refine contDiffAt_pi.mpr fun i=>?_; let L:X→L[ℝ] G.Color:= (ContinuousLinearMap.proj i).comp F.symm.toContinuousLinearMap; exact (show ContDiffAt ℝ ω _ (L 0) from by rw [map_zero]; exact Native.Chart.speeds G (ran z i)).comp _ L.contDiff.contDiffAt
    let w(t:ℝ):=t•x; have hb: ContDiffAt ℝ i (fun t=> K (w t)) 0:=(show ContDiffAt ℝ i K (w 0) from by rw [show w 0=0 from zero_smul ..]; exact hk.of_le le_top).comp _ (show ContDiffAt ℝ i w 0 from contDiffAt_id.smul contDiffAt_const)
    unfold bill; change Tensor.coeff (A ∘ (fun t=> K (w t))) i 0 _=A _; rw [Tensor.coeff_linear A _ hb]; apply congr_arg A; unfold Tensor.coeff Tensor.diagonal; simp only [Tensor.coeff,_root_.smul_apply,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; simp only [Finset.prod_const_one,one_smul]; apply congr_arg ((i.factorial:ℝ)⁻¹ • ·); exact Next.Foundations.iteratedDeriv_on_line (hk.of_le (m:=i) le_top) x
-- convert ∇ in Primary indexes
noncomputable def grad (k:Site n → G.Color): Positions (Primary n G):=(panel G n).symm (gradient k)
lemma speedStart(k:Site n→ G.Color) : speedsK k 0=grad k:=by
    let w(i:Body 1 n):= Native.Chart.speed G (ran k i) 0; apply (panel G n).injective; rw [grad,(panel G n).apply_symm_apply]; funext e; change w (e.1,Exterior.coord e.2) = _; obtain ⟨i,j⟩:=e; unfold w; rw [Native.Chart.begins]; unfold ran AnalyticBridge.VerifiedReset.gradient; dsimp only; rw [show axisEquiv.symm (Exterior.coord j)=j from axisEquiv.symm_apply_apply j]
variable (R:PathData G)(p:Clip)(F:Nesting G n)(q:ℕ){S:ℝ → Config G n→ℝ}(h:Trend S F R p q)
local notation "Ω"=> tariff n q p R F
variable (i:ℕ)(hx:i≤q)
include hx h
lemma driven (x:X)(k:Site n→G.Color) : impulse n G (µ i (tariff n q p R F)) x (grad k)= -∑ j∈Finset.range i, impulse n G (µ j (tariff n q p R F)) x (Tensor.diagonal (Tensor.coeff (speedsK k) (i-j) 0) x):=by
    have he:= ascends k R p F q x h i hx; rw [Finset.sum_range_succ,i.sub_self,billFlight, show Tensor.diagonal _ _= grad k from (Tensor.coeff_apply_zero ..).trans (speedStart k)] at he; simp_rw [billFlight] at he; exact eq_neg_of_add_eq_zero_right he
lemma gentle (hG:G.Simple) (k:Site n→G.Color)(x:Positions (Primary n G)) : rim (joy Ω i) x (grad k)=0:=by
    let ℱ(j):= joy Ω j; have hF(j:ℕ): ContDiff ℝ ω (ℱ j) := vent ..
    have he(j:ℕ)(he:j≤q): fderiv ℝ (ℱ j) 0=0:=zero_hit ((hF j).of_le (show (2:WithTop ℕ∞)≤ ω from le_top)|>.contDiffAt) hG (fun t=>Eventually.of_forall (inh R p F q h j he t)) -- edit F shadow
    let fK(j)(v:X):= fderiv ℝ (ℱ j) v; let V' j:= Tensor.diagonal (Tensor.coeff (speedsK k) (i-j) 0); let Q'(j)(v:X):= fK j v (V' j v)
    have hp (j:ℕ): ContDiff ℝ 2 (V' j):=Tensor.diag_smooth ..; let X':=Finset.range i
    have hD(j)(hh:j∈X') : (HasFDerivAt (𝕜:=ℝ)) (Q' j) 0 0:=by
        have hk:j < i:= Finset.mem_range.mp hh; have hA: V' j 0=0:= by unfold V'; have he:= Tensor.homogeneous (Tensor.coeff (speedsK k) (i-j) 0) 0 0; simpa only [zero_smul,zero_pow (show i-j≠0 from by omega)] using he
        have hx : ContDiffAt ℝ 1 (fK j) 0:= (hF j|>.contDiffAt).fderiv_right (by simp)
        have ht:= (hx.differentiableAt (by simp)).hasFDerivAt.clm_apply ((hp j).differentiable (by simp) 0).hasFDerivAt
        refine HasFDerivAt.congr_fderiv ht (ContinuousLinearMap.ext (fun y=>?_)); simp only [_root_.add_apply]; change (fK j 0) _ + (fderiv ℝ (fK j) 0 y) (V' j 0)=0; rw [hA,show fK j 0=0 from he j (hk.trans_le ‹i≤q›).le]; simp
    let f':= fK i; let z:= ContinuousLinearMap.apply ℝ ℝ (grad k); have h1 : (z ∘ f') = fun v=> -(∑ j∈X',Q' j v):= funext (fun v=> driven R p F q h i hx v k)
    have h2:= HasFDerivAt.fun_sum hD; have h3 : fderiv ℝ (z ∘ f') 0=0:=by rw [h1,h2.fun_neg.fderiv]; simp
    have hc:ContDiffAt ℝ 1 f' 0:= (hF i|>.contDiffAt).fderiv_right (by simp); rw [fderiv_comp _ z.differentiableAt (hc.differentiableAt (by simp)), z.fderiv] at h3; exact congr_arg (fun i:X→L[ℝ]ℝ=>i x) h3
end YM.MSbar.Wave
