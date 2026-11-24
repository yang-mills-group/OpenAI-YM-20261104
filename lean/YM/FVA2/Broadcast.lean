import YM.FVA2.AllPanels

/-!
# One more layer: Full open pipeline on all later steps

`Fk.read` calls on true Hessian and Penalty plus the remaining intraweight
(formal, finite extension by polynomials). No fictitious positivity
hypothesis on a covering-real Planet. `Branches` from construction is used.
Includes all markers as a Ticket, coarse and even inserted at precise labels,
no comparison of off-inversion or actual conditioning calls. `first_any` for
actual first rung with unweighted bare Wilson step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bk
open Filter Topology Function Finset MeasureTheory FormalOPE.RG10
open FormalOPE.RG10.MarkovChain OpenSlots
open RGComparison.Core16 RGComparison.Core16.Lumen Lumen.Planet
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable {G:Gauge} {c f:Side}

section smooth
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (Q:Quadratic E)

def targeting (x:E) := Q.flourish x/2
lemma targeting_hot : ContDiff ℝ ω (targeting Q):= by
    let f:= LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp Q.P)
    exact (f.contDiff.clm_apply (g:=fun x=>x) contDiff_id).div_const _
lemma targets (x:E) : jet (targeting Q) 2 x=Q.flourish x/2:= by
    have he(a:ℝ): targeting Q (a • x)=a^2 * targeting Q x:=by
       unfold targeting Quadratic.flourish; simp only [map_smul,LinearMap.smul_apply, smul_eq_mul]; ring
    have hx:= directions (f:=targeting Q) ((targeting_hot Q).contDiffAt.of_le le_top) x; simp_rw [he] at hx; exact (congr_fun (hx.unique (Aspiration.single (targeting Q x) 2)) 2).trans (if_pos rfl)
end smooth

variable {S: StepData c f}(H:S.patch.Branches S.kernel G)
variable (P: Inside S.ratio) (t:S.Choices) (J:ChartRatio G) (hJ:LocalRatio J)
variable (U:Unmasked G f) (w:PowerSeries ℝ)
local notation "I"=> Blocking.Index S P
local notation "E"=> Cross (G:=G) S P
local notation "F"=> Flats G f
local notation "Y"=> Flats G c
local notation "η"=> blankRight (G:=G) P
local notation "μ"=> tangent G I
local notation "Q"=> gated P U t w

def rays := targeting (Quadratic.drag η U.Q) + term w 0 • (substep (G:=G) P t)
local notation "M"=> rays P t U w
include H
lemma rays_hot : ContDiffAt ℝ ω M 0:= (targeting_hot _).contDiffAt.add ((subReady P t H).const_smul (term w 0))
lemma rays_pay (x:E × Y) : (Q).flourish x= 2*jet M 2 x:= by
   let z:=term w 0; let V:E × Y→ℝ:= substep P t
   rw [rays, Inherit.plus (a:=targeting _) (b:= term w 0 • substep P t) 2 (targeting_hot _).contDiffAt ((subReady P t H).const_smul (term w 0)), Inherit.times _ z (subReady _ _ H), targets]
   change (drag η U.Q).flourish x + (genesis w V).flourish x= _; rw [Quadratic.native]; unfold V z; ring

variable [Nontrivial G.Color] (y:Flats G c)
def budgets (T':S.Choices)(x:Fk.Door G I):=rays P T' U w (sideChange y x)
def expense_x (u:ℝ) (T': S.Choices) (x:Forge.Sky G (Blocking.Index S P)) : ℝ := budgets P U w y T' (u,fun i=> (@Lumen.axis G).symm (G.curvature (x i)))
-- This `expense` is for checking germ and not used at all off chart. Not
-- asserting positive cost there nor a smooth catalog on any fixed real ball.

def other (y:Y) : Planet (formalShelf y M) f I Unit S.Choices:=
   formalPanel y M (fun i=>i.val.val.1) (fun _ t' _=> if t=t' then 1 else 0) (expense_x P U w y)
local notation "A"=> other P t U w y
local notation "W"=> rayBlock J M
local notation "Ω"=> receipt P t J w U
omit H in
lemma other_costume : Fk.rise A =ᶠ[𝓝 0] mount y M := costume ..
lemma shared : ∀ᶠ x:Fk.Door G I in 𝓝 0,∀ t':S.Choices, expense_x P U w y x.1 t' (Fk.spread x.2)=Fk.lapse A x:= by
    filter_upwards [eventually_all.mpr (fun i:I=> ((continuous_apply i).tendsto ((0:Direction G I))).comp ((continuous_snd.tendsto (0:Fk.Door G I)))|>.eventually axis_eq), pricedHere H P t y, other_costume P t U w y] with x hx he hv
    intro t'; change x.1^2+Fk.lapse A x= x.1^2+ M (sideChange y x) at hv
    have hcp: substep P t' ((sideChange y) x)=substep P t ((sideChange y) x):= by
       apply add_left_cancel (show wilson (expLinks G _ (OpenSlots.extend P x.2))+ substep P t' ((sideChange y) x)= wilson (expLinks G _ (OpenSlots.extend P x.2))+substep P t ((sideChange y) x) from ?_)
       have h:= (he t').trans (he t).symm; unfold earnings at h; rw [dressStep] at h; exact h
    rw [expense_x, add_left_cancel hv, budgets, show ((x.1),fun i=> (@Lumen.axis G).symm (G.curvature (Fk.spread x.2 i)))=x from Prod.ext rfl (funext hx)]
    exact congr_arg ((targeting (Quadratic.drag η U.Q)) (sideChange y x)+ (term w 0 :ℝ) * ·) hcp

variable (A0:Ticket (Cross (G:=G) S P × Flats G c)) -- including all marks in that transfer first multiplied
-- Name exported for precise inputs
abbrev multis (f₁:Ticket (E × Y)) := priceEntries y (extras M J f₁) A J
local notation "τ"=> multis P t J U w y
include H hJ
variable (r:(core (gated P U t w)).RespectsPrice)
local notation "p"=> ambient J y Q r
lemma ledger (f₁:Ticket (E×Y)) :
    PowerSeries.C p * Stack.read y (uptake Q μ r f₁)= PowerSeries.mk (Fk.birth A J) * τ f₁:= by
    rw [savings_y y J hJ M (rays_hot H P t U w) Q (rays_pay H P t U w) r (other_costume P t U w y),mul_assoc (C p), change_body Q M (rays_hot H P t U w) (rays_pay H P t U w) r J hJ y (other_costume P t U w y) f₁];
lemma budget_r : PowerSeries.C p * Stack.read y (Update P t J w U r).W= PowerSeries.mk (Fk.birth A J) * τ Ω:= ledger H _ _ _ hJ U _ _ _ _
omit H hJ [Nontrivial G.Color] in
lemma readFit (V: Ticket Y)(he:Splice.incline V): constantCoeff (Stack.read y V)=1:=by rw [← coeff_zero_eq_constantCoeff_apply, reading_term, coeff_zero_eq_constantCoeff_apply, he]; rfl
lemma seats (a: incline U.W) : Stack.read y (Broadcast P t J w U r A0)= τ (Ω*A0) * (τ Ω)⁻¹:= by
    let B' := PowerSeries.mk (Fk.birth A J); let Z:=Update P t J w U r; let b':= Stack.read y (Broadcast P t J w U r A0)
    have hh: Z.W * Broadcast P t J w U r A0= uptake Q μ r (Ω*A0):= fit_eq _ _ _ _ _ (OpenSlots.along hJ w a)
    have hc:= budget_r H P t J hJ U w y r
    have he : constantCoeff Z.W=1 := funded hJ w a _
    have hz:0 < constantCoeff (PowerSeries.C p * Stack.read y Z.W):= by rw [map_mul,constantCoeff_C, readFit y Z.W he,mul_one]; exact positive_amount y J hJ Q r
    have hl : constantCoeff (B'*τ Ω)≠0:= by rw [show B'*_= _ from hc.symm]; exact hz.ne'
    rw [map_mul,mul_ne_zero_iff] at hl
    apply eq_mul_inv_iff_mul_eq hl.2|>.mpr
    apply mul_left_cancel₀ (show B'≠0 from fun h'=>hl.1 (h' ▸ map_zero _));
    rw [← ledger H P t J hJ U w y r (Ω*A0)] -- B' doesn't match
    rw [← hh,mul_comm b',← mul_assoc, ← hc,map_mul (Stack.read y),mul_assoc]
-- Route link layout & prices at precisely same weights
variable {j l:Type}[Fintype j][Fintype l]
omit H [Nontrivial G.Color] in
theorem revenue_step (D:Sync.Layout j F)(B:Sync.Layout l Y)(a: incline U.W):
    Route.Bulk.income (Sync.Engine J t P D B w U r).joint (Sync.Engine J t P D B w U r).vertices = Sync.digital B (Update P t J w U r).W:= by
    change Route.Bulk.income _ (Sync.voltage D B _ _) = Sync.digital B (uptake Q μ r Ω); rw [Sync.stationed]; exact Sync.revenue _ _ _ _ _ _ (Sync.pursue P) μ (preserve_boost _ (OpenSlots.along hJ w a))
end YM.FVA2.Bk
