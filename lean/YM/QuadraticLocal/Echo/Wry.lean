import YM.QuadraticLocal.Echo.Village
import YM.AllOrder.Wheel.Languish
import YM.QuadraticLocal.Poetry.Fish
/-!
# Bind output of auxiliary analytic evaluator to the same normalized Markov push
 Especially not the `exp of sum of projected k-terms` (effective vacuum aspect). For unmasked
 single packets on ALL configurations. On true aperture narrower than these need full polynomial lift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type*} {V:Type}[Fintype V][DecidableEq V]{G:Gauge} {k j e Nℓ:ℕ} {a f σ b Z τ A:ℝ} {n l:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
open Spot Trace Sunrise
namespace Wry
open Comparison.RG02 Bulk Marker
variable (S:StepData n l)(P:RG.Rep G l)(I:V→Loan)(p:∀ i:V,Atom G (I i).r)(s:V→Site l)(U:Config G n)
local notation "Fr"=> Sunrise.Focus.census V
abbrev timeF (i:V):Config G l→ℝ:= fun (U:Config G l)=> ((Coat.gStep P.beta)^ (I i|>.power))⁻¹* Loan.letter (I i) (p i) (s i) (Coat.gStep P.beta) U
local notation "σ" i:max=> Wry.timeF P I p s i
variable (u: (Sunrise.Focus.census V).Mode)
-- Actual log of these specified marks; keep full normalized vs tilted Kappa. Revenue
abbrev sector (V': Finset V) (U:Config G l):= ∏ i∈V', timeF P I p s i U
abbrev holding := fun U:Config G l=> P.eval U* sector P I p s u.val U
abbrev vote (U:Config G n):ℝ:= S.push P.beta (Wry.holding P I p s u) U /(S.push P.beta P.eval U)
def theatre (u:(Sunrise.Focus.census V).Mode)(U:Config G n):= ∑ x∈Multi.shards (Sunrise.Focus.census V) u, Page.sigmaM V x* ∏ t∈x.val,Wry.vote S P I p s t.val U
set_option quotPrecheck false
local notation "Sh"=> sector P I p s
lemma sector_envelope (x:Finset V) : RG.Envelope (sector P I p s x) := Function.const _ (by
 induction x using Finset.induction_on with | empty=> unfold sector; simp_rw [prod_empty]; exact Envelope.const _ | insert i q hi ih=> unfold sector at *; simp_rw [prod_insert hi]; exact ((Envelope.const _).mul (Loan.bound ..)).mul ih
  ) (inferInstance : Fintype V)
variable (hp:∀ x,(p x).Invariant)
include hp
lemma guisses (x:Finset V): GaugeInvariant (sector P I p s x):= Function.const _ (Function.const _ (fun i u=> Finset.prod_congr rfl (fun k _=> congr_arg (_*·) (Loan.natural (I k) (p k) (s k) (Coat.gStep P.beta) (hp k) i u))
  ) (inferInstance : Fintype V)
  ) (inferInstance : DecidableEq V)
omit hp
section nominal
variable {K:KernelChoices}{P:Patch}{r:Stage}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}{q:ℝ→ℝ}{J:ℕ}
variable (W:Aux.Name G P K q J r k U) (M:Page W I) {f:Age→ℝ}(h:W.Civil f)(hv:∀ i,(M.mark i).Invariant)
set_option quotPrecheck false
local notation "ν₁" => W.forest.order G
local notation "N"=> W.forest.Slice G
local notation "Uo"=> W.tilt
local notation "κ"=> W.data
abbrev cal :V→Site W.f:=fun i=> M.path i (M.root i)
local notation "γ"=> Wry.cal I W M
local notation "Φ"=> Page.yardP W I M
include h hv
lemma paid (x:W.X) : Wry.vote W.data W.tilt I M.mark (Wry.cal I W M) u (Desk.night x)= Page.priceEntry W I M x u := by
 obtain ⟨C,hP,hQ⟩:= h.price; let f i:=(M.mark i); let y:= Desk.night x; let z:= W.tilt; let K:=(κ).push W.beta z.eval y; let a:= W.attends x; let A (v:N):= W.forest.drape v
 let u':= sector z I M.mark γ u.val; let g':= Wry.holding z I M.mark γ u
 have hp(x:N): u' (A x)= (∏ i∈u.val, (Page.yardP W I M i x)):= rfl
 let H:= W.loom.large.1; have hX : GaugeInvariant g':=fun i u=> congr_arg₂ (·*·) (Presented.lawful_gi hQ.cap i u) (guisses z I M.mark γ hv _ i u)
 have hμ : RG.Envelope g':= ((z.envelope hQ.cap).mul (sector_envelope z I M.mark γ _)); apply congr_arg₂ (·/·) _ (W.tilt_record h x|>.2.2.2); change W.data.push W.beta g' y=∫ i:W.forest.Slice G,W.newZ x i*(∏ q∈u.val, Page.yardP W I M q i) ∂ν₁
 rw [W.forest.pushing ((κ).isKernel H W.beta) _ y hX (hμ.integrable _) (fun k U=> W.data.covary H k W.beta U y)]; apply MeasureTheory.integral_congr_ae; filter_upwards with i; let v:=A i; change W.data.density _ _ _*(z.eval v*u' v)= _; have he: W.newZ x i=W.data.density W.beta v y* z.eval v:= by rw [W.tilt_eq]; rw [← mul_assoc]; exact congr_arg (· * _) (Fare.total ..); -- rfl `z`
 rw [he,mul_assoc]; rfl
-- convert establishment
set_option maxHeartbeats 200000
lemma entrance : Page.hostel W I M=(theatre W.data W.tilt I M.mark (Wry.cal I W M) (Focus.onto (univ:Finset V)))∘ Desk.night:= by
 ext1 x; unfold theatre Page.hostel; simp_rw [Function.comp_apply,paid I _ W M h hv x]
end nominal
end Wry
end YM.QuadraticLocal.Echo
