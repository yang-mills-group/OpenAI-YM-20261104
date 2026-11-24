import YM.WilsonCoeffUV.Step.Ward.Auxiliary
/-! Ward equality on finite bulk tori, as anti-aliased origin identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge PowerSeries
open FreeResolvent Tree
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)

/-- pair relation for even a SINGLE given transformation s,b. Equality
of scalar expressions under rooted analytic maps. Handles kernels carried via
same label separately. -/
def rollTest (p p': Ink (Woods G c))(s:Signed)(b:Site c): Prop := ∀ {Y:Type}[Fintype Y] {q:Lawn Y→Site c→G.El} {X X': Lawn Y→ TreeVars G c}, TurnsG s b q X X' →
    train (spool X) p=train (spool X') p'

def Warded (u:Ink (Woods G c)) : Prop:= ∀ s b,rollTest u u s b
lemma top_turn {H: FreeResolvent.FaceRow}(h:H.acts c=1) : Warded (flash (sprig (eWilson (G:=G) (c:=c)) 2)) := by
  intro s b Y hf q X X' E; have hZ:= w_jets (G:=G) h
  have hp := sprouts_move hZ.1 hZ.2.1
  have H : ∀ᶠ w:Lawn Y in 𝓝 0, eWilson (X w)=eWilson (X' w) := by
    filter_upwards [E.shift] with w hw; simp_rw [eWilson,hw,energy_gauge,energy_pull]
  apply mul_left_cancel₀ (a:=(PowerSeries.X : Ink Y)^2) (pow_ne_zero _ X_ne_zero)
  conv_lhs=>arg 1; arg 1; rw [← train_X (spool X)]
  conv_rhs=>arg 1; arg 1; rw [← train_X (spool X')]
  rw [← map_pow,←map_pow,←map_mul,←map_mul,hp,traveling X E.g₀ E.f₀ _ W_green,traveling X' E.g₁ E.f₁ _ W_green]; exact jet_congr H

section
variable {Z:Type} [Fintype Z] [DecidableEq Z]
variable (M: Matrix (Woods G f) (Woods G c) ℝ)
variable (s:Signed)(b:Site c)(q:Lawn Z→Site c→G.El)(X X':Lawn Z→TreeVars G c)
local notation "Ξ"=> surf S F s b q
local notation "θ"=> wend S F M X X' Ξ
local notation "Φ"=> fanWest (X:=Active G F) (spool X)
local notation "Ψ"=> reroll (spool X') (spool θ)

lemma west_train (h:Green X)(hz:X 0=0): Φ=train (spool (west S F X)) := by
  have hh i: spool (leftArm (U:=Active G F) (V:=Z)) i=path (Sum.inl i) := by
    have he: leftArm (U:=Active G F) (V:=Z)= fun u=> leftFlag (Active G F) Z *ᵥ u := (funext left_hit).symm
    classical
    rw [he,spool_board,loom_pin,Finset.sum_eq_single (Sum.inl i)]<;>simp +contextual [leftFlag]
  rw [fan_reroll, show (fun i : Active G F=>path (Sum.inl (β:=Z) i))=spool leftArm from funext fun i=> (hh i).symm]
  exact roll_shawl _ X leftZero h hz
lemma east_train (E:TurnsG s b q X X') : Ψ=train (spool (east S F M X X' Ξ)) := by
  have h := wend_zero S F M X X' _ (surf_zero S F s b E) E.f₀ E.f₁
  exact roll_shawl θ X' h E.g₁ E.f₁

lemma rolled_loom {U V W:Type}[Fintype U][Fintype V][Fintype W](h:Lawn U→ Lawn V)(he:h 0=0)(hh:Green h)(K:Matrix W V ℝ)(p) :
    train (spool h) (loom K p)=train (spool (fun u=>K*ᵥ h u)) p := by
  classical
  rw [← spool_loom]; exact DFunLike.congr_fun (spool_chain h (fun v=>K*ᵥ v) he (by simp) hh (board _)) _

lemma wire_orbit (hM:M=reveal G S F*((reveal G S F).transpose*M)) (E:TurnsG s b q X X') (p p':Ink (Woods G f)) (h:rollTest p p' s (S.ratio.embed b)) :
   Φ (loom (camSlice G S F M) p)=Ψ (loom (camSlice G S F M) p') := by
  have he := turn_complete S F M X X' s b q E hM
  rw [west_train S F X E.g₀ E.f₀,east_train S F M s b q X X' E,rolled_loom _ (west_zero S F X E.f₀) (west_diff S F X E.g₀),rolled_loom _ (east_zero _ _ _ _ _ E.f₀ E.f₁ _ (surf_zero _ _ _ _ E)) (east_diff _ _ _ _ _ E.g₀ E.f₀ E.g₁ _ (surf_diff _ _ _ _ E))]; exact h he

lemma wind_price (e:S.patch.Branches S.kernel G) (hM:M=reveal G S F*((reveal G S F).transpose*M))(E:TurnsG s b q X X') :
    let L:= loom (panSlice G S F M) (flash (sprig (jointPen G S) 2))
    Φ L=Ψ L := by
  intro L
  classical
  let u:= west S F X; let v:=east S F M X X' Ξ
  let T:=panSlice G S F M; let U w:= T *ᵥ u w; let V w:= T *ᵥ v w
  let k := jointPen G S
  let j:= flash (sprig k 2)
  let g:=fineRot S F M X s b q
  have hp := (pen_jets G S e); have hW:= turn_complete S F M X X' s b q E hM
  have hu: Green u := west_diff S F X E.g₀; have hv:Green v:= east_diff _ _ _ _ _ E.g₀ E.f₀ E.g₁ _ (surf_diff _ _ _ _ E)
  have hU:u 0=0:=west_zero S F X E.f₀; have hV:v 0=0:=east_zero S F M X X' E.f₀ E.f₁ _ (surf_zero S F s b E)
  have h₁ : Φ L=train (spool U) j:= by rw [west_train S F X E.g₀ E.f₀]; exact rolled_loom u hU hu T j
  have h₂ : Ψ L=train (spool V) j:= by rw [east_train S F M s b q X X' E]; exact rolled_loom v hV hv T j
  rw [h₁,h₂]; let C:= Active G F⊕Z;
  have hz : ((PowerSeries.X: Ink (Joint G f c))^2)*j=jet k:= sprouts_move hp.1 hp.2.1
  apply mul_left_cancel₀ (a:=(PowerSeries.X: Ink C)^2) (pow_ne_zero _ X_ne_zero)
  have θ₀ : Tendsto (fun p=> camSlice G S F M *ᵥ u p) (𝓝 0) (𝓝 0) := hW.f₀ ▸ hW.g₀.continuousAt.tendsto
  have θ₁ : Tendsto (fun p=> camSlice G S F M *ᵥ v p) (𝓝 0) (𝓝 0) := hW.f₁ ▸ hW.g₁.continuousAt.tendsto
  have hc := penalty_same S e
  have hk : ∀ᶠ w : Lawn C in 𝓝 0, k (U w)=k (V w):= by
    filter_upwards [hW.shift,(rightGreen (X:=Active G F) (Y:=Z)).continuousAt E.shift,θ₀.eventually hc,θ₁.eventually hc] with x hx hy ha hb
    apply price_channel S e _ _ s b (g x)
    · unfold V U T; rw [arm_pan,arm_pan]; exact hx
    · unfold V U T; rw [arm_pan, arm_pan,fine_rot_roots]; exact hy
    · unfold U T; rw [arm_pan]; exact ha
    unfold V T; rw [arm_pan]; exact hb
  have hu' : Green U:= (show ContDiffAt ℝ ω (fun a=>T*ᵥ a) (u 0) from by rw [hU]; exact board T).comp 0 hu
  have hv' : Green V:= (show ContDiffAt ℝ ω (fun a=>T*ᵥ a) (v 0) from by rw [hV]; exact board T).comp 0 hv
  conv_lhs=>arg 1; arg 1; rw [← train_X (spool U)]
  conv_rhs=>arg 1; arg 1; rw [← train_X (spool V)]
  rw [← map_pow,←map_pow,←map_mul,←map_mul,hz,traveling U hu' (by unfold U; rw [hU]; simp) _ (show Green k from penSmooth G S e), traveling V hv' (by unfold V; rw [hV]; simp) _ (show Green k from penSmooth G S e)]; exact jet_congr hk
end
end YM.WilsonCoeffUV.Power
