import YM.Juniper.OrbitPrice.Change
/-!
 # Contraction, full output assembly in a quantitative model comparison test

 Unlike showing a pure analytic `Lineage`, this calls Dales on the actual
 mixed input and ACTUAL β. Hilbert completion used just for defect estimates,
 and then work on real histories again. Approx doesn't have to be a Future.
 Orientation & Valves needed by this test DIFFER by period, but same for
 actual/model step. Norm is actual Budget. This upgrades the qcomp
 integration contract for e inherited (not analytic). When using a
 perturbative model readers MUST still establish the rendering in these
 exact supports & equivariance, and its local defect (and its relationship
 to independent PT). Don't infer from comparing sums of reshuffled debts.
 Does not remove the actual K gas. Also reconstructs full comparison output
 incl vacuum scalar in both real transports. Carries their possible scalar
 difference (per site).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
open UVExtension Function Filter Set Lattice MeasureTheory
open RG Shoot Supply Pressure Precision Tree Wilson PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Org Progress.DirectedRecipe Time Input Tabernacle Dales Guild Camp Spire Oriel Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε u:ℝ}
local notation "B" => A.B.a
local notation "p" => A.B.a.budget m
local notation "s!"=> m+1
local notation "p!"=> A.B.a.budget s!
variable (hG:G.Simple) (t:Crest R ε) (H:Tour R N m n ε) (T: Paperwork R.shape ε u A.delay)
    (d:Cham A.B.a (m+1) n) {d':Cham A.B.a m n}(h : Tour.Hind R hG t H d d') (a : ℝ) {β:ℝ}
    (ht : Lamppost.InsideB (A.B.a.clock.hatBeta (m+1)) β)

private lemma distance (x y : Valve s! n A.B.a d) (z:ℝ) :
    ‖river B s! n d (z,x)-river B s! n d (z,y)‖=‖place B s! n d x-place B s! n d y‖:=by
  change max ‖(z:ℂ)-(z:ℂ)‖ ‖place B s! n d x-place B s! n d y‖=_; rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]

local notation "W!"=> Valve s! n A.B.a d
local notation "L!"=> place B s! n d
local notation "L"=> place B m n d'
local notation "Ω"=> H.choiceV R hG t d h
local notation "Λ"=> H.claim R d
local notation "τ"=> A.B.a.clock.op m n
variable {x y: Valve (m+1) n A.B.a d} {d₀: Valve m n A.B.a d'}
include T H ht hG t h
lemma take_in (hx:‖L! x‖<rim) (hy:‖L! y‖<rim) :
    ‖L (Ω y β)-L (Ω x β)‖≤u*‖L! y-L! x‖ ∧ |Λ y β - Λ x β| ≤ worth B s! * ‖L! y-L! x‖ ∧
    ‖L (Ω y β)‖ ≤ u ∧ |Λ y β| ≤ worth B s! := by
  obtain ⟨⟨F,hF⟩,U,hU⟩ := Dales.shelves R hG t H d T ht h
  let r(z:W!) := river B s! n d (0,z)
  have hp(z:W!)(h:‖L! z‖<rim): r z∈ Oriel.Charted.Grip:= mem_ball_zero_iff.mpr (max_lt (show ‖(0:ℂ)‖<rim by norm_num [rim]) h)
  have he (z:W!)(h': ‖L! z‖<rim): U (r z)= L (Ω z β) ∧ F (r z)=(Λ z β:ℂ):=by
    have hy : art (A.B.a.clock.hatBeta s!) β 0=β:=by unfold art; ring
    rw [show U (r z)= _ from hU.ray (0,z) (hp z h'), show F (r z)= _ from hF.ray (0,z) (hp z h')]; simp only [Dales.marble,Dales.flowing,hy, and_self]
  obtain ⟨hl,hK⟩:=he x hx; obtain ⟨he,hF'⟩:= he y hy
  have hpU:=hU.bounds.2.2 (r y) (hp y hy) (r x) (hp x hx); have HpF:=hF.bounds.2.2 (r y) (hp y hy) (r x) (hp x hx); have he': ‖r y-r x‖= ‖L! y-L! x‖:= distance d y x 0
  have hf0:= hF.bounds.2.1 (r y) (hp y hy); rw [hF',Complex.norm_real] at hf0
  rw [he,hl,he'] at hpU; rw [hF',hK,← Complex.ofReal_sub, Complex.norm_real,he'] at HpF
  exact ⟨hpU,HpF,he ▸ hU.bounds.2.1 (r y) (hp y hy),hf0⟩

variable (hr: β∈ RG.Shoot.band A.B.a (m+1))(hx:‖place A.B.a (m+1) n d x‖<rim)
    (hy:‖trueE y‖<rim)
omit T H ht hG t h
local notation "J"=> merge y x
include hx hr
lemma accepts_budget : Reality B s! n d x β:= ⟨hr,hx.le.trans (by norm_num [rim])⟩
omit hr
include hy
lemma merge_grip: ‖L! J‖<rim:=by rw [total_two]; rw [total x] at hx; exact max_lt hy ((le_max_right ..).trans_lt hx)
include hr
lemma accepts_merge : Reality B s! n d J β:= accepts_budget d hr (merge_grip d hx hy)
omit hx hr hy
section evaluation
local notation "Ų"=> mount R N s! n (merge y x).val β a
-- exact E-factorized model perturbation on ALL FIELDS
lemma separated (U: Config G (A.B.a.S.side s! n)) :
    (mount R N s! n x.val β a).eval U=(Ų).eval U* Real.exp (- (Tabernacle.floor p! (x-y).val).additive p! U) := by
  rw [Rep.eval,Rep.eval, mul_right_comm _ ((Ų).activities.gas _ _),← Real.exp_add]
  congr 1; congr 1; unfold Rep.exponent; simp only [Dales.mount]; rw [bare_E, packet y x U]; ring
end evaluation

local notation "X₀"=> Ω x β
local notation "Y₀"=> Ω (merge y x) β
local notation "β₀"=> β + A.B.kin.alpha N m + Λ x β
local notation "β₁"=> β + A.B.kin.alpha N m + Λ (merge y x) β
local notation "σ₀"=> mount R N s! n x.val β a
local notation "σ₁"=> mount R N s! n (merge y x).val β a
local notation "θ" => mount R N m n (X₀|>.val) β₀ (flatRate B m n σ₀)
local notation "ϑ" => mount R N m n (Y₀|>.val) β₁ (flatRate B m n σ₁)
-- the step version is already useful: no small-field-only caveat.
include H hG h t hr hx
lemma eject : (θ).eval = (τ).push β (σ₀).eval ∧
    0<(τ).push β (σ₀).eval 1 ∧
    (θ).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) ∧
    (θ).activities.KBound p (Return.forcing A.B m) := by
  set d₀:=d; have hv := accepts_budget d₀ hr hx
  have he: θ = H.speck R d hv a := by rw [Tour.choiceV,dif_pos hv, Tour.around,Tour.claim,dif_pos hv]
  rw [he]; exact synthetic R hG t H _ hv a
include hy ht T
lemma actual_defect :
    let Y : Hold B m n d':= L (Y₀); let X : Hold B m n d':= L (X₀)
    ‖X-Y‖≤u*‖trueE x-trueE y‖ ∧ |β₀-β₁| ≤ worth B s!*‖trueE x-trueE y‖ ∧
    (ϑ).eval = (τ).push β (σ₁).eval ∧ 0 < (τ).push β (σ₁).eval 1 ∧
    ‖Y‖≤u∧(ϑ).activities.KBound p (Return.forcing A.B m):=by
  intro Y X
  have hv := merge_grip d hx hy
  obtain ⟨hg,hP,hX,_⟩:= take_in R hG t H T d h ht hv hx
  obtain ⟨hp,hε,hG,hh⟩:= eject R hG t H d h a hr hv
  refine ⟨?_,?_,hp,hε,?_,hh⟩
  · rw [total_diff] at hg; exact hg
  · rw [add_sub_add_left_eq_sub]; rw [total_diff] at hP; exact hP
  exact (take_in R ‹G.Simple› t H T d h ht hx hv).2.2.1 -- shadow
end YM.Juniper.Native
