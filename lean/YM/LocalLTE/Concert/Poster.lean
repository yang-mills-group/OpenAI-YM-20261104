import YM.LocalLTE.Concert.Budget
/-!
# Compile additional analytic prerequisites. Uniform WAGES, no estimate left conditional. Measured AFTER Y shift on adjacency (hat). Doesn't take ancestry shots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
open LocalLTE.Fan LocalLTE.Fan.Pastel LocalLTE.Port LocalLTE.Port.LoopBank Coat
variable {G:Gauge}(L:Side)(p M:ℕ) {c L' d:ℝ}
variable (b m k:ℕ)(J μ ε κ:ℝ) (P:Stage)(i:ℕ) {z:ℝ} (hz:Reliable G κ z)(hc:0≤J)(hm:0≤μ)(he:0<ε)(hi:ε<(i:ℝ)/4)
open LocalLTE LocalLTE.FrameBox Animals
-- pre analytic.Halls. iris includes coverage radius.P. Strength surcharge EXACT.
local notation "p0"=> (slotPay G J b P.order P.power)
def Poster (G:Gauge)(L:Side)(b m k:ℕ)(J μ ε κ:ℝ)(P:Stage)(i:ℕ)(x:ℝ) : Prop:= 1 ≤ betaF G x L ∧4*(b+1) ≤ radiusB (betaF G x L) ∧ b+1 ≤ L.val*radiusB x ∧ let t:= betaF G x L; let q:= Urns.divisor t; let s:= t^μ; let z:= t^(-ε); let r:= neat t μ; let d:=slotPay G J b P.order P.power; ∀ V:Type,∀ [Fintype V], Fintype.card V ≤ k →∀ (P':BudgetPoint),P'.order=P.order →P'.power=P.power → P'.supportExponent=P.supportExponent → P'.threshold=temp t→ capacity P' V (LoopBank.costAP m r P' b (d+z) s) (LoopBank.costAP m r P' b z s) q z (t^ε) (L.val*radiusB x) ≤ t^(-(1:ℝ)) ∧ gross m b P' (q^2) (t^μ*d) ≤ z*q ∧ ∀ (n:Side),2*(b+1) < n.val →2*(2*b) ≤ n.val → ∀ (o:Site n)(l:Walk)(L:G.Mat→L[ℝ]ℝ), l.length ≤ b →stop o l=o→ (∀ v w:G.El,L (G.mat (v*w*v⁻¹))=L (G.mat w)) → (∀ x,‖L x‖ ≤ J*‖x‖)→∀ (Y:Grove o), P'.supBounds o (neighbors (b+1) o) (traceT o l L - Hall.shave Y b κ i (traceT o l L)) z
include hz hc hm he hi
lemma castle : ∀ᶠ x in atTop, Poster G L b m k J μ ε κ P i x:=by
    have hv:= Work.E09.betaF_growth G L
    have hT:= Port.springs G J ε hc he.le P.power P.order b i hi hz
    filter_upwards [hv.eventually_ge_atTop 1,hv.eventually (Work.E07.radiusB_eventually (4*(b+1))),Work.E07.radiusB_eventually (b+1),summerB L b m k J μ ε P hc he,hv.eventually (cope (G:=G) b m J μ P hc hm (-ε)), hv.eventually hT] with x hx ht he hp hZ hT
    refine ⟨hx,ht,he.trans (Nat.le_mul_of_pos_left _ L.property),?_⟩
    intro t q s z r d V H hv B hB hh hζ hυ
    exact ⟨hp V hv B hB hh hζ,(hZ _ hB hh hζ).trans_eq (mul_comm q z), hT _ hB hh hυ⟩ -- H.instance line ?
-- param after.Poster.more general for ANY d: symbolic.K callers can shrink.
omit hz hc hm he hi
structure Prereq (G:Gauge) where
    jobs : ∀ {s:Sheet G}{D:Rolls s}{P:Protection D},Delays P→ℝ→Prop
    buys : ∀ {s:Sheet G}{D:Rolls s}{P:Protection D}(V:Delays P) (κ:ℝ),(∃ v:ℝ,Reliable G κ v)→∃ Y: Delays P,DelayLe V Y∧ ∀ W:Delays P,DelayLe Y W→jobs W κ
structure Posters {G:Gauge}{s:Sheet G}{D:Rolls s}{P:Protection D}(b m k:ℕ)(J μ ε κ:ℝ)(i:ℕ)(Y:Delays P):Prop where
    pays: ∀ j l, StepStages j l→∀ x ≥ Y.betaEntry j, Poster G (D.L j) b m k J μ ε κ (s.profile j) i x
variable (G)
def valence (hc₁:0≤J)(hm₁:0≤μ)(he₁:0<ε)(hi₁:ε<(i:ℝ)/4) :Prereq G where
    jobs:= fun Y κ=> Posters b m k J μ ε κ i Y
    buys:=by
                   intro s D P V κ hk
                   obtain ⟨W,-,hx,hX⟩:= collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ (fun a h=> castle (D.L j) b m k J μ ε κ (s.profile j) i hk.choose_spec hc₁ hm₁ he₁ hi₁)
                   exact ⟨{V with betaEntry:=W},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun U h=>⟨fun j v ht y he=> hX j y ((h.beta _).trans he) v ht⟩⟩
end YM.PhysicalNext.Repeat.Mallow
