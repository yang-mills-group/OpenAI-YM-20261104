import YM.AllOrder.Floe.Posto
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D:RG.Supply.Rolls X.p}(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) -- x stage fine from D
local notation "B" => X.K
local notation "A" => X.p.profile
local notation "p" => X.p.profile x
local notation "q" => X.p.profile y
local notation "K" => X.p.kernel
local notation "O"=> X.O
local notation "Ωz" => abs (X.K.Ω x)
local notation "Ωy" => abs (X.K.Ω y)
variable (D) (hx:4≤x)
set_option quotPrecheck false
local notation "P" => Mural.sheet X.p D hx
local notation "C₀" => Pane.cloak D x
local notation "P'" => Plateau.Ticket (P) K O (A x) (A y) (Pane.cloak D x)
local notation "s₁" => R.pre k x
local notation "s₂" => R.pre k y
local notation "T" => tape (k+2)
local notation "I"=> Card D R x y hx k
-- audit arg x implicit λ.
local notation "X0" => fun i:I=> Card.extra i
namespace Roots
/-! require one System chosen after θ then Pay.Including Interest.Renormalizable coordinate. Later choose extra waits & floor.L.Mortar; Costume.More allowed keep. -/
structure Tab (D:RG.Supply.Rolls X.p) where
    income (x y :ℕ)(hx:4≤x)(hY:StepStages x y)(k)(h: k+2≤y)(hh:Nonempty (Card D R x y hx k)): Income D R x y hx k
variable (hL:∀ x,R.Rise x ((D.L x).val:ℝ))
lemma options (g:G.Simple) : Nonempty (Tab R D):= by choose f hf using fun x y (hx:4≤x) (he:StepStages x y) => (fun k (h:k+2≤y) (H:Nonempty (Card D R x y hx k))=> Income.earn_round D R x y hx (Classical.choice (Plateau.Art.has (N:=k+2) (G:=G) _ _ _ (by omega))) H g he); exact ⟨⟨f⟩⟩
local notation "Z₀"=> strengthP
variable (G₀:Roots.Tab R D)
abbrev Lease (G₀:Roots.Tab R D)(x y:ℕ)(t:ℝ):=∀ (hx:4≤x)(he:StepStages x y)(k:ℕ)(h:k+2≤y)(H:Nonempty (Card D R x y hx k)), Income.Bears D R x y hx (G₀.income x y hx he k h H) t
lemma leases (hx:4≤x)(he:StepStages x y) (h:k+2≤y)(H:Nonempty (Card D R x y hx k)) (hc:R.Rise x ((D.L x).val:ℝ)) : ∀ᶠ t in atTop, Income.Bears D R x y hx (G₀.income x y hx he k h H) t:= Income.bearing D R x y hx _ hc h he
lemma prepay (G':Tab R D)(he:StepStages x y) (hx:R.Rise x ((D.L x).val:ℝ)): ∀ᶠ t in atTop, Lease D R G' x y t:= by
 by_cases h:4≤x; swap; · exact Eventually.of_forall fun _ H=> (h H).elim
 let v(k:ℕ)(t:ℝ) := ∀ (hh:k+2≤y)(H:Nonempty (Card D R x y h k)), Income.Bears D R x y h (G'.income x y h he k hh H) t
 have hp k:∀ᶠ t in atTop,v k t:= by
    by_cases hp:k+2≤y; swap; · exact Eventually.of_forall fun _ hv=> (hp hv).elim
    by_cases hQ:Nonempty (Card D R x y h k); swap; · exact Eventually.of_forall fun _ hv hF=> (hQ hF).elim
    exact (leases D R x y G' h he hp hQ hx).mono fun i hi _ _=>hi -- arg order
 filter_upwards [(eventually_all_finset (range (y+1)) («p»:=v)).mpr (fun k hk=>hp k)] with i hi; intro hh hr k hc hW; exact hi k (mem_range.mpr (by omega)) hc hW
/- pay Crest initial at Stage hatBeta x with no consumption from post phases. Also allow ANY q from higher post future.X. Real.
-/
def Cresting (x:ℕ)(t:ℝ):=∀ k:ℕ,k+2≤x→∀ i∈Age.scope (k+2), Quoted (Crest.tile (A x).clip G i) (R.pre k x i) (authority k i (strengthP t))
lemma mountains(i: Age) : ∀ᶠ t:ℝ in atTop, ∀ t'≥t, Quoted (Crest.tile (A x).clip G i) (R.pre k x i) (authority k i (Z₀ t')):= by
 let B':= Crest.allowance (A x).clip G i.r (R.pre k x i)
 obtain ⟨b,hb⟩:= Filter.eventually_atTop.mp (((tendsto_pow_atTop (Nat.add_one_ne_zero (level k i))).comp (beyond.comp deep_x)).eventually_ge_atTop B'); refine Filter.eventually_atTop.mpr ⟨b,fun u hu i' he => Quoted.narrow (Crest.info (A x).clip G i (R.pre k x i)) le_rfl (hb _ (hu.trans he))⟩
lemma heights (x:ℕ): ∀ᶠ t in atTop,Cresting R x t:= by
 have hx k: ∀ᶠ t in atTop, ∀ i∈Age.scope (k+2), Quoted (Crest.tile (A x).clip G i) (R.pre k x i) (authority k i (Z₀ t)):= (eventually_all_finset (Age.scope (k+2))).mpr fun i hi=>(mountains R x (k:=k) i).mono fun v hv=> hv v le_rfl
 filter_upwards [(eventually_all_finset (range (x+1))).mpr (fun k _=>hx k)] with t ht k hp i hi; exact ht k (mem_range.mpr (by omega)) i hi
open RG.Supply
-- each Entrance p. only when post-L. use Φ in harmony with Bank.Carries.Contact. Keep B.L.
structure Receives {p':Protection D}(V:Delays p') : Prop where
    due (x y:ℕ)(hx:StepStages x y)(t:ℝ) : V.betaEntry x ≤ t→ Lease D R G₀ x y t
    cream (x y:ℕ)(hx:StepStages x y)(t:ℝ) : V.betaEntry x ≤ t → Cresting R y t
include hL
lemma summit {p':Protection D}(V:Delays p') : ∃ W:Delays p', DelayLe V W ∧ ∀ Y:Delays p',DelayLe W Y → Receives D R G₀ Y:= by
 obtain ⟨x,-,hx,h⟩:= collect_upper V.betaEntry (fun j t=> ∀ i, StepStages j i→ Lease D R G₀ j i t∧Cresting R i t) (fun j=>eventually_transitions _ _ _ (fun y he=> (prepay D R j y G₀ he (hL _)).and (heights R y)))
 exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ hv=> ⟨fun a y hF i hi=> (h _ _ ((hv.beta a).trans hi) y hF).1, fun a y hF i hi=> (h _ _ ((hv.beta a).trans hi) y hF).2⟩⟩
end Roots
end PlanV
end YM.AllOrder.Floe.Step
