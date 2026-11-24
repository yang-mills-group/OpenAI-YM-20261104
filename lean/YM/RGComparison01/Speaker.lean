import YM.RGComparison01.Whistle
import YM.RGComparison01.Ports
/-!
# The local offer carrying each held cluster

 Mirror symmetry via honest per-address costing. Does not first move address
 masks to a site rep wholesale without reserving +1 forced costs. All masks
 still required on sums. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
    {κ: Chi}
variable {c f C F L₀: Side}
section word
variable {S:StepData c f} {T : Tube G S} {R : RG.Rep G f}
    {I : Cash W s a L₀ X o U T R} (D : Cabinet ι I b)
namespace Cabinet
def vote (p : Cabinet.Record D ℓ) := ((D.ground p.val).card:ℝ)⁻¹
def payable (κ : Chi) (p : Cabinet.Record D ℓ) (V : Config G c) := - (vote D p) * stream I κ V (covers D p)
def offered (κ:Chi) (ℓ k : ℕ) (x:Site c) (V:Config G c) := ∑ p ∈ (D.podium ℓ k).filter (fun p=> x∈ D.ground p.val),payable D κ p V
def tot (κ : Chi) (ℓ k : ℕ) (γ : ℝ) := Meadow.atlas (offered D κ ℓ k + Meadow.garner T.down T.low R.beta γ (radiusB s) k)
lemma rotates (κ : Chi) (ℓ k : ℕ) (γ:ℝ) (x:Site c) (u:Config G c) (θ : Signed) (z:Site c): D.tot κ ℓ k γ x (pull θ z u)= D.tot κ ℓ k γ (Lattice.affine θ z x) u:= Meadow.astrolabe _ x u (θ,z)
end Cabinet
end word
section period
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC:C.val=c.val*M} {he : 2≤ c.val}
variable {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} {R : RG.Rep G f} {R':RG.Rep G F}
  {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b} {Z : χ → ι}
    (L':Relay (A:=A) (D:=D) hC he Z)
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
local notation "Sg" => Cabinet.garage b ℓ
variable (hB:4*Cabinet.garage b ℓ<c.val)
variable (hq : T'= re T) (V:Config G c) (hv : RG.flags (Pressure.temp s) V=∅)
set_option quotPrecheck false
local notation "V'" => (L).low.links V
include hq hB L' hv
variable {i i' k k' : ℕ} {C₁ d₁ v₁ Y₁ A₁ b₁ r₁ B₁ q₁ C₂ d₂ v₂ Y₂ A₂ b₂ r₂ B₂ q₂ : ℝ}
    (N:Captain I i C₁ d₁ v₁ Y₁ A₁ b₁ r₁ B₁ q₁ k κ) (J:Captain I' i' C₂ d₂ v₂ Y₂ A₂ b₂ r₂ B₂ q₂ k' κ)
include N J
namespace Relay
lemma travels (x : Site C) (p : A.Record ℓ) (hp : x∈ A.ground p.val) :
    Cabinet.payable A κ p (V')= Cabinet.payable D κ (recycle L' hB x p hp) V := by
  let t := recycle L' hB x p hp
  have ht : (V')=(L).low.links V:=rfl
  have hx' : RG.flags (Pressure.temp s) (V')=∅ := by ext i; rw [show i∈RG.flags (Pressure.temp s) (V') ↔ _ from flagged hC V i (by have h:= I.laws.data.room.buys; omega) (Pressure.temp s),hv]; simp
  have hs:L'.recycle hB x p hp=t:=rfl
  rw [Cabinet.payable,Cabinet.payable,show Cabinet.vote D _ = _ from congr_arg (fun p:ℕ=>(p:ℝ)⁻¹) (L'.voices hB x p hp)]
  have hT : stream I κ V (D.covers t)=I.trainedPool κ V (D.covers t) := by
    exact Eq.symm ((congr_fun (N.permitAverage (D.covers t)).2.2.2.1 V).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hv]; simp)))
  have hX : stream I' κ (V') (A.covers p)= I'.trainedPool κ (V') (A.covers p) := by
    exact Eq.symm ((congr_fun (J.permitAverage (A.covers p)).2.2.2.1 (V')).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hx']; simp)))
  rw [hs,hT,hX]; apply congr_arg; unfold Cash.trainedPool Gas.term
  apply congr_arg₂ HDiv.hDiv _ rfl; apply congr_arg₂ HMul.hMul
  · rw [← A.stars, ← D.stars]; exact L'.constant p.val _ (by omega) x (A.extent p x hp)
  apply prod_congr rfl; intro i _
  exact L'.illuminates x _ (by omega) _ ((A.within p.val i).trans (A.extent p x hp)) hq V κ hv (p.property.poses i) (t.property.poses i)

lemma all_offer (x:Site C) (n : ℕ) : A.offered κ ℓ n x (V')=D.offered κ ℓ n ((L).low.cut x) V:= L'.sum_prism hB x n (fun p hp _=> travels L' hB hq V hv N J x p hp)
lemma itinerary (x : Site C) (γ : ℝ) (n:ℕ) (hb:R'.beta=R.beta) :
    A.tot κ ℓ n γ x (V')=D.tot κ ℓ n γ ((L).low.cut x) V:= by
  let y:= (L).low.cut x
  let f (θ:Seat c):= D.offered κ ℓ n ((Meadow.spin θ).symm y) (θ.view V) + Meadow.garner T.down T.low R.beta γ B n ((Meadow.spin θ).symm y) (θ.view V)
  unfold Cabinet.tot Meadow.atlas; change _=likely f
  rw [← Meadow.revolving hC f]; apply congr_arg likely; funext θ; simp only [f,Pi.add_apply]
  have hf θ: Macrame.splitter (Deck.divides hC) ((Meadow.spin θ).symm x)=(Meadow.spin (Meadow.pinch hC θ)).symm y:= Meadow.inverts ..
  rw [show θ.view (V')=(L).low.links ((Meadow.pinch hC θ).view V) from Meadow.estuary hC V θ]
  apply congr_arg₂ HAdd.hAdd
  · rw [← hf]; exact all_offer L' hB hq _ (Meadow.covers_field _ V hv) N J _ _
  rw [hb,← hf]; subst T'; exact Meadow.garner_pack hC ..
end Relay
end period
end YM.RGComparison01
