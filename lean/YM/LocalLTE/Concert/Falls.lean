import YM.LocalLTE.Concert.Flakes
import YM.LocalLTE.Slide.Ice
/-!
# REAL chart trace proposal. Forecast and its price.

Carrier from Hall.shave in physical canonical coordinates. Threshold uses *this* prior Budget. No supported price conversion dropped.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side} (P:Rep G n) (B:BudgetPoint)
variable {V α :Type}[DecidableEq V]{R:Census V} (X:Layers P R α)
open FrameBox Grove Cabana
open AnalyticBridge VerifiedReset Collection
open Animals ConnectedActivityE6 Blaze Brush
-- sparsity extension constants signs. Angle ℓ as physical Taylor local.Eye prepaid. Use side=L=1, NO shifting.
abbrev oneQ : Side:= ⟨1,by decide⟩
lemma oneShift (G:Gauge)(x:ℝ): Pressure.betaF G x oneQ=x:=by simp [Pressure.betaF,oneQ]
open Pressure Push.SectorMeasure
variable (G) {κ k:ℝ}
lemma springs (c e:ℝ)(hc:0≤c)(_h0:0≤e)(p j b i:ℕ)(hi:e < (i:ℝ)/4)(h:Reliable G κ k): ∀ᶠ x:ℝ in atTop,∀ (B:BudgetPoint), B.order=j→B.power=p → B.threshold=temp x → ∀ (n:Side),2*(b+1) < n.val →2*(2*b) ≤ n.val → ∀ (o:Site n)(l:Walk)(L:G.Mat→L[ℝ]ℝ), l.length ≤ b →stop o l=o→ (∀ v w:G.El,L (G.mat (v*w*v⁻¹))=L (G.mat w)) → (∀ x,‖L x‖ ≤ c*‖x‖)→∀ (Y:Grove o), B.supBounds o (neighbors (b+1) o) (traceT o l L - Hall.shave Y b κ i (traceT o l L)) (x^(-e:ℝ)):=by
    let Y:=oneQ; obtain ⟨M,hM,hF⟩:= Port.trestleT G b (i+j) c hc -- order 
    let v:= -(1/4:ℝ); let f:=fun _: ℝ=> b+1; let g:=fun _:ℝ=> M
    have hp: 0+v*(i:ℝ)< -e:=by unfold v; linarith
    filter_upwards [Hall.prunes G Y j p i (n:=f) (g:=g) (by exact Rate.const ((b+1:ℕ):ℝ)) h (show -(7/16:ℝ) ≤ v by norm_num [v]) (show v < 0 by norm_num [v]) (Rate.const _) hp, eventually_ge_atTop (1:ℝ)] with x ht hx B hB he hx' n hn hK o l L hl hL hS hb Z
    have hv:∀ U: Directions G n,‖U‖ < Inset.cone v (betaF G x Y)→ Brush (i+j) ((1:ℝ)*M) 1 (traceT o l L ∘ soloV) U:=by
       rw [one_mul,show Y=oneQ from rfl,oneShift]; exact fun U h=> hF n o l L hl hb U (h.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (show v ≤ 0 by norm_num [v]))) -- lemma
    have hA:B.threshold ≤ 2*Pressure.fiery G x Y:=by unfold fiery; rw [← show oneQ=Y from rfl, oneShift,← hx']; linarith only [B.threshold_pos]
    have hz:= ht B he hB hx' hA (b+1) b le_rfl le_rfl n o hn hK Z _ (traceDuty B o l b L hl hL hS) 1 zero_le_one hv
    rwa [← show oneQ=Y from rfl,oneShift,one_mul] at hz
-- color amplitude
noncomputable def Hue (s:ℝ)(b:Bool) : ℝ →L[ℝ] ℂ := s • (ContinuousLinearMap.id ℝ ℝ).smulRight (ink b)
lemma hueVal (x s:ℝ)(b:Bool) : Hue s b x=(↑(s*x):ℂ)* ink b:=by unfold Hue; simp [Complex.real_smul,mul_assoc]
lemma hueCost (x s:ℝ)(b:Bool): ‖Hue s b x‖=‖s‖*‖x‖:=by rw [hueVal,norm_mul,tintX,mul_one,Complex.norm_real,norm_mul]
section
variable {G}{n:Side}{r:ℕ}{κ:ℝ}{a:ℝ}
variable {x:Site n}(X:Grove x)(f:Config G n→ℝ)
lemma hueReg (P:BudgetPoint)(S:Support n)(h:P.Regular S f)(s:ℝ)(b:Bool): P.Regular S (Hue s b ∘ f):=by
    let F':=Hue s b
    have hh Vp h': Push.Local.Chart P.order (F' ∘ f) Vp:= F'.contDiff.contDiffAt.comp _ (h.smooth _ h')
    exact ⟨fun u v hp=> congr_arg F' (h.sites _ _ hp), F'.continuous.measurable.comp h.borel,fun t U=>congr_arg F' (h.symmetry ..),hh,fun V h A l ht=> Next.Foundations.left_has A ht (hh V h)⟩
lemma hueRad (P:BudgetPoint)(S:Support n)(h:P.Regular S f)(s:ℝ)(b:Bool)(y:Site n)(hq:P.supBounds y S f a): P.supBounds y S (Hue s b ∘ f) (‖s‖*a):=by
    refine ⟨mul_nonneg (norm_nonneg _) hq.1,fun V hV l hl hv=>?_⟩; rw [Push.Local.left_linear _ _ (h.smooth V hV) hl,hueCost]; exact mul_le_mul_of_nonneg_left (hq.2 _ hV l hl hv) (norm_nonneg _)
lemma hueDiff (s:ℝ)(b:Bool)(g: Config G n→ℝ): Hue s b ∘ f-Hue s b ∘ g=Hue s b ∘ (f-g):= by funext i; exact (map_sub ..).symm
lemma huesPam (S:ℕ) (h:Price.Replicated X r κ S f)(s:ℝ)(b k:Bool): Price.Replicated X r κ S (Port.scaleQ k ∘ Hue s b ∘ f):=by
    let V':= (Port.scaleQ k).comp (Hue s b)
    have hz: scaleQ k ∘ Hue s b ∘ f=(V' 1) • f:=by
       funext i; change V' (f i)= V' 1 * f i; conv_lhs=> rw [show f i=f i • (1:ℝ) by simp]
       rw [map_smul]; exact mul_comm (f i) _
    rw [hz]; exact Price.rp_scale _ _ h
end
end YM.LocalLTE.Port
