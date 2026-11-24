import YM.LocalLTE.Moor.Patch
import YM.LocalLTE.Moor.Whisk
import YM.LocalLTE.Moor.Marks
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
/-! Bison.kin consumer of high-order terrain. Paid on the SAME stencil and
 K companions (core reads full additive log only eventually). Additional
Hessian/value/marker extractions need own booking. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Patch
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open Marlin Trio Slide Height
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L:Side} {J₁ j i m n W₁ w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side}
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Stars,Trio.Offer G (Y i)) (p: Patch.read Y G)
    {S:StepData c f} {T:Tube G S} {P:Teller G} {W:ℝ} {X : ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W} {a' μ D e a b L₀ v Z x K₀ c' c₁ σ Λ β:ℝ}
    {R : RG.Rep G f} (H: Cash W x μ L X o a T R)
    (γ:ℝ) (ℓ:ℕ) (m:ℕ)
-- within common orbit and patch comparison. spelling Cons.
local notation "χ" => Chi.canonical
local notation "η" => Meadow.intern H
local notation "d₀" => Meadow.studioN ℓ X.halo (radiusB x)
abbrev marked (z:ℕ) : Pipes G c:= Marlin.lodge (Beam.marquee H B) z (2*z)
abbrev inventory := Meadow.timbresN η («χ»:=Chi.canonical) γ ℓ m -- caution notation param
abbrev failure : Site c → Config G c → ℝ:= Trio.insightN (J₀:=ℓ) B η γ m Q z fa

def deposit : Tap G c:= Marlin.bison (inventory H γ ℓ m) (Trio.ornament Q fa) (failure B Q z fa H γ ℓ m)
def market := Marlin.pluck B (Patch.marked B H z)
def fresh := Marlin.poursP B (marked B H z) (Patch.deposit B Q z fa H γ ℓ m)
-- Reading on the new Reg labels: contributions split as three EXACT log
-- components. Model independent of inherited R; occupies no H address inside
-- Civ. Retain neg sign. Need next normalizations in early→post transcript.
def ancestor (i:ℕ) : Config G c→ℝ:= Sum.elim (Meadow.heats H χ γ) 0 (leanU c i)
def planned (c:Side) (i:ℕ) : Config G c→ℝ := Sum.elim (fun _ => 0) (Song.choir (fun x=> -(mural Q p x))) (leanU c i)
def tributary (i:ℕ) : Config G c→ℝ:= Sum.elim (Meadow.ash H χ ℓ m γ) (Song.choir (light fa Q p)) (leanU c i)

lemma revenue : (fresh B Q z fa H γ ℓ m).logRead = ancestor H γ + tributary Q fa p H γ ℓ m + planned Q p c := by
  -- preserve native idempotent hard interactions, not read twice
  funext j
  unfold fresh Marlin.poursP deposit Marlin.bison; dsimp only [Pi.add_apply,Function.comp_apply, inventory,Tap.regular]
  unfold Patch.ancestor Patch.tributary Patch.planned -- maybe unfold semantic
  cases he:Marlin.leanU c j with
  | inl v=> dsimp only [Sum.elim]; rw [Meadow.allotted]; ext V; simp
  | inr v=> ext U; dsimp only [Sum.elim,Pi.add_apply,Pi.zero_apply,Song.choir,Pi.smul_apply,Patch.light,smul_eq_mul,Function.comp_apply,Pi.neg_apply]; ring

variable (hp : Collection.Local (posting B H) B (Song.plusone H (Meadow.intern H) Chi.canonical γ) K₀ D)
    (hk : ∀ s b, Nonempty (((Beam.marquee H B).read (Meadow.timbresN (Meadow.intern H) («χ»:=Chi.canonical) γ ℓ m)).Moves s b)) -- prove
    (hG: Ingredients (Patch.marked B H z) (Marlin.dummy (Patch.deposit B Q z fa H γ ℓ m)) (raiser B) 0 Z)
    (ht: Meadow.Budget B (Beam.marquee H B|>.reg) (Meadow.timbresN (Meadow.intern H) («χ»:=Chi.canonical) γ ℓ m|>.logRead) a') -- bind
    (hQ:Meadow.Budget B (leap (c:=c) z) (Trio.ornament Q fa) L₀)

include hp hG ht hk
theorem exact_new (P:PathData G) (d:Clip) (τ:ℝ) (V:Config G c): earlyValue (posting B H) P d B (Song.plusone H (Meadow.intern H) χ γ) β τ γ V=
      earlyValue (market B z H) P d B (fresh B Q z fa H γ ℓ m) β (τ-Meadow.baronyN H ℓ χ m γ 0 1) γ V:= by
  apply Marlin.carries B (Beam.marquee H B) z (2*z) (inventory H γ ℓ m) (Trio.ornament Q fa) (failure B Q z fa H γ ℓ m) V (R:=posting B H) (plusone H (Meadow.intern H) χ γ) (fun i=> ⟨rfl,rfl⟩) P d β _ _ _ hG ht ?_ hp.transforms hk
  intro U; exact Trio.levyN B η _ m Q z fa _ _ _ hp
omit hp
include hQ
lemma localStock : Collection.Local (market B z H) B (fresh B Q z fa H γ ℓ m) (a'+turnFee B*L₀) Z :=
  Marlin.sous hG (Marlin.reg_bison (Beam.marquee H B) z (2*z) _ _ _ ht hQ) (fun s b=> Marlin.reeds _ _ _ _ _ _ s b (hk s b|>.some))
omit hG hk ht hQ
-- main decomposition preserved after Marlin ordering
lemma precision (hB: Meadow.Budget B (Beam.marquee H B).reg (Meadow.ash H Chi.canonical ℓ m γ) e) (hT: Meadow.Budget B (leap (c:=c) z) (light fa Q p) L₀):
    Meadow.Budget B (market B z H).reg (tributary Q fa p H γ ℓ m) (e+turnFee B*L₀):= by
  let U': Collection.Source G c:= ⟨Meadow.ash H Chi.canonical ℓ m γ,(Meadow.timbresN (Meadow.intern H) («χ»:=Chi.canonical) γ ℓ m).hardRead⟩
  exact Marlin.reg_bison (Beam.marquee H B) z (2*z) U' (light fa Q p) (failure B Q z fa H γ ℓ m) hB hT
lemma historical (hB: Meadow.Budget B (Beam.marquee H B).reg (Meadow.heats H Chi.canonical γ) e):
    Meadow.Budget B (market B z H).reg (ancestor H γ) e:= by
  let t:Collection.Source G c:= ⟨Meadow.heats H Chi.canonical γ,(Song.plusone H η χ γ).hardRead⟩
  have hf : Meadow.Budget B (leap (c:=c) z) (0:Trio.Offer G c) 0:= by
    refine ⟨0,fun i=>?_,fun i=>?_⟩; · simp [SumBudget]
    exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  have hx:= Marlin.reg_bison (Beam.marquee H B) z (2*z) t _ 0 hB hf; rw [mul_zero,add_zero] at hx
  suffices hp: Patch.ancestor H γ=(Marlin.bison t 0 0).regular by rw [hp]; exact hx
  funext i; unfold ancestor; change _=Sum.elim (Meadow.heats H χ γ) (choir (0:Site c→ Config G c→ ℝ)) (Marlin.leanU c i); cases Marlin.leanU c i; rfl
  ext i; simp [Sum.elim,Song.choir]
end YM.LocalLTE.Patch
