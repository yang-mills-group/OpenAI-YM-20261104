import YM.RG01Estimate.Scope
/-!
 # Transfer of auxiliary promise price on shape-compatible stencils.
 Starts with short auxiliary push theorem (on THAT same stencil and same
 rendered forecasts). Charges at all seams of ROI; no purchase needed
 beyond stencil from the model. No positivity dropped. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Promise
open Function Filter Set Metric Finset Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior Abacus
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}
section warp
variable {α:ℕ}{G:Gauge}{c:Side}(V:Config G c) {A:Listing G c} {W:ℕ→ Config G c→ℝ}{B:BudgetPoint}(U: Rack A α W)
lemma frothV {sf:ℝ} (hV: flags B.threshold V=∅)(h: Meadow.Budget B A.reg W sf) : Push.Local.Chart B.order (Trio.froth U.polygon) V := by
  rw [show Trio.froth U.polygon=∑ i:Site c,U.polygon i from funext fun i=> (Finset.sum_apply ..).symm]
  exact (Meadow.regularA (X:=univ) _ fun i hi=> CouplingShape.reg_extend (U.plating B h i) (subset_univ _)).smooth V (by unfold Healthy; rw [hV]; simp)

variable {Q : ℕ→ Config G c→ℝ} {f: Config G c→ℝ} {σ u' s':ℝ}(h : Meadow.Budget B A.reg Q s')
     (hq: Meadow.Budget B A.reg W u') (ht: ∀ V∈ Boulevard.sunny B,f V=σ-Trio.froth U.polygon V-Boulevard.throng Q V)
     (hp: V∈ Boulevard.sunny B)
include ht h hq U hp
lemma habit : Push.Local.Chart B.order (Boulevard.stillA f) V:= by
  let k:= increment V; have hv : Tendsto k (𝓝 0) (𝓝 V):= by
      have h : k 0=V:= Work.G07.at_zero_increment ..; rw [← h]; exact (show Continuous k from continuous_pi (fun i=> (G.lieExp_cont.comp (continuous_apply i)).mul (continuous_const (y:=V i)) )).continuousAt
  let W:=Trio.froth U.polygon; let a:=Boulevard.throng Q
  have h':= frothV V U (smoky hp) hq; have h₀:= Boulevard.commemorates h V hp|>.1
  let t:= fun y=> σ-W (k y)-a (k y)-f 1
  have hz:ContDiffAt ℝ (B.order:WithTop ℕ∞) t 0 := (((contDiffAt_const (c:=σ)).sub (g:=W ∘ k) h').sub (g:=a ∘ k) h₀).sub contDiffAt_const
  apply hz.congr_of_eventuallyEq; filter_upwards [hv (Boulevard.sky B|>.mem_nhds hp)] with y hy
  change f (k y)-f 1=_; rw [ht (k y) hy]
end warp
variable {c f:Side}{A:Listing G c}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
      (k:S.Choices)(r:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)(t:ℝ)
local notation "X" => Positions (Uniform.Primary c G)
variable (v:ℝ × Positions (Uniform.Primary c G)→ ℝ)(H:Poll.Body (Precision.Key F G)→ ℝ× Positions (Uniform.Primary c G)→ℝ)
    {L:Side} {R a i d j:ℕ} {β τ y u δ σ θ m α γ ℓ γ₁ W V n d' D w v' s s' q C C' P' : ℝ}
variable (U:Config G f→ℝ) (x: Positions (Uniform.Primary c G))
section shape
-- Loft keeps bills, available at all promised apertures
structure Loft (t z:ℝ)(P:BudgetPoint)(L:Side)(G:Gauge)(Q:ℝ) : Prop where
    pay : ∀ (c:Side)(x:Positions (Uniform.Primary c G))(β v:ℝ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
     (F:Config G c→ E), let b:=gStep β; betaF G t L /2 ≤ β → β≤2*betaF G t L → 1≤ z → ‖x‖≤ b*z → P.threshold≤ 2* Pressure.fiery G t L →
      Push.Local.Chart P.order F (Boulevard.actual x) → Brush P.order v 1 (fun y=> F (Boulevard.actual (b • y))) (b⁻¹ • x) →
     ∀ l:List (Directions G c),l.length≤ P.order → (∀ i∈l, ‖i‖≤ P.threshold)→ ‖leftDerivs F l (actual x)‖ ≤ v*Q
    extend : ∀ (c:Side)(x:Positions (Uniform.Primary c G))(β v:ℝ)
        (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]
        (f:Config G c→ E), betaF G t L/2≤ β → ‖x‖≤gStep β*z → P.threshold=Pressure.temp t → flags P.threshold (actual x)=∅ → Push.Local.Chart P.order f (actual x) →
        (∀ y:Positions (Uniform.Primary c G), ‖y‖≤ ‖x‖ → actual y∈ Boulevard.sunny P → ∀ l:List (Directions G c),l.length ≤ P.order → (∀ i∈l, ‖i‖ ≤ P.threshold) → ‖leftDerivs f l (actual y)‖ ≤ v) →
        ∀ l:List (Directions G c),l.length ≤ P.order→(∀ i∈l, ‖i‖ ≤ P.threshold) → ‖leftDerivs f l (actual x)‖ ≤ v
lemma talk (j:ℕ) (Y:ℝ→ℝ)(hk:Cookie G L Y):∃ W:ℝ→ℝ,Cookie G L W ∧ ∀ᶠ t in atTop,∀ P:BudgetPoint,P.order=j→Loft t (Y t) P L G (W t):= by
   obtain ⟨Q,hq,H⟩:= Receipt.travel G L Y j hk; refine ⟨Q,hq,?_⟩; filter_upwards [H,Receipt.rim G L Y hk] with t ht he P hp; subst j; exact
     ⟨(fun c x β v E _ _ _ f=> ht c P x β v E f), fun c x β v E _ _ f => he c x β v P E f⟩

-- Same T report, local stage θ. Seams authenticated.
variable {F':Collection.Source G c}{P U' V': ℕ→ Config G c→ℝ} (p:Rack A a U')
variable (h : ∀ Z,S.push β U Z=earlyValue A T.down T.low B F' β θ γ Z)
    (hf:F'.logRead=P+V'+U')(he: Meadow.Budget B A.reg P v')(hU:Meadow.Budget B A.reg U' s')
    (hV:Meadow.Budget B A.reg V' q)(hT:T.down.Bounds T.low C C' P')
    {B' : BudgetPoint} (hQ : Card T F k r O (forecast T P β γ) v H R B.order B β y u δ σ) (hp:0<β)(hb:gStep β ≤ 1)
    (hx : ∀ x: Positions (Uniform.Primary c G), ‖x‖+1< y→ actual (gStep β • x)∈ Boulevard.sunny B→ Receipt.Article T F B' r t d' D y β s α x U H i j ∧ Receipt.Note T F B' k r O t d' D y β s α W w V n x i j R B.order)
    (hk : ∀ z:Poll.Body (Precision.Key F G),∀ x∈ ball (0:Positions (Uniform.Primary c G)) y,H z (0,x)=1)
    (hL : Loft t y B L G m) (hΒ : betaF G t L/2 ≤ β)(hβ : β≤2*betaF G t L)
    (hM : flags B.threshold (actual (gStep β • x))=∅) (hX : ‖x‖+1<y)

local notation "b" => gStep β
local notation "K" => (Fintype.card (Site c):ℝ)
def prize (R:ℕ)(β V σ δ m q n:ℝ) := ((2:ℝ)*((gStep β^R*V+gStep β^R*σ)+β*((R+2:ℕ)*δ)))*m+2*(n*q)
include h hf he hU hV hT hQ hp hb hx hk hL hΒ hβ hM hX T F k r
lemma mural (hY:B.threshold≤2*Pressure.fiery G t L)(hr:B.threshold=Pressure.temp t) : ∀ l : List (Directions G c), l.length ≤ B.order → (∀ i∈l,‖i‖≤B.threshold)→
      ‖leftDerivs (Boulevard.stillA (Trio.froth p.polygon)) l (actual (b • x))‖ ≤ prize R β V σ δ m q K := by
   let f:=action (S:=S) (forecast T P β γ) U β
   let W':=Trio.froth p.polygon; let Z:=b • x; have ht:0<b:=(gS β hp).1
   have h0:= norm_nonneg x; have hm :1≤ y:=by linarith
   have hz:‖Z‖=b*‖x‖:=by unfold Z; rw [norm_smul,Real.norm_of_nonneg ht.le]
   have hy:‖Z‖≤ b*y:=hz.trans_le (mul_le_mul_of_nonneg_left (by linarith) ht.le)
   have h':=header T B U p h hf he hU hV hT
   have hc : Push.Local.Chart B.order (Boulevard.stillA W') (actual Z):= (frothV (actual Z) p hM hU).sub contDiffAt_const -- may edit
   let g:= 2*((b^R*V+b^R*σ)+ β*((R+2:ℕ)*δ)); let n':= g*m
   apply hL.extend _ Z β _ ℝ _ hΒ hy hr hM hc
   intro z hz' hZ
   change actual z∈sunny B at hZ
   have hκ : ‖b⁻¹ • z‖ ≤ ‖x‖:= by
       rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]; exact (inv_mul_le_iff₀ ht).mpr (hz'.trans_eq hz)
   have hp : ‖b⁻¹ • z‖+1<y:=by linarith only [hκ,hX]
   have hf' : Push.Local.Chart B.order (Boulevard.stillA f) (actual z) := habit _ p hV hU h' hZ
   let Y':=Boulevard.stillA f; have hK := still_bill T F B k r O t (forecast T P β γ) v H U (b⁻¹ • z) hQ ‹0<β› hb hx hk hp (smul_inv_smul₀ ht.ne' z|>.symm ▸ hZ)
   have he := hL.pay _ z β _ ℝ Y' hΒ hβ hm (hz'.trans hy) hY hf' hK
   exact Boulevard.tightens (A:=A.reg) hZ hV h' hf' he
end shape
end YM.RG01Estimate.Promise
