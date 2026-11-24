import YM.QuadraticLocal.Pry
import YM.QuadraticLocal.Travel
/-!
 # Extra radii shrinkage in second flag merger, to pay exact mask changes
 Full paid K includes consumption at these radii afterwards. Proof of retained
 cap at previous radii may need additional post-block power, e.g. at finite horizon.
 Repeated admission can conserve that slack by using `pay_after` only at the
 point where restoring all close-window losses; the intermediate steps should
 use the smaller weights. Hard already merges with the ACTUAL vacuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Progress.DirectedRecipe
open RemainderComparison
namespace Travel
variable {I V:Type}{G: Gauge}{n c L:Side}{x v e κ w a b d q z:ℝ}{α:Type*}
variable {A0:Teller G}{Q:ConnectedActivityE6.Target G A0}{Horizon:ConnectedActivityE6.Target.Order G w}
variable {S:StepData c n}{D:Pressure.Tube G S}{P:Rep G n}{P':Rep G c}
open ConnectedActivityE6
variable (H:Cash w x κ L Q Horizon z D P)
variable (E₀: ℕ→ RegularAddress c)(V₀:ℕ→ Config G c→ℝ) -- select unmarked first
open Lyric Muse Serif Spire Push.SectorMeasure
local notation "O"=> Chi.canonical
set_option quotPrecheck false
local notation "Ω"=> (Match.staple (H:=H) («J»:=H) rfl rfl rfl)
local notation "Xa"=> Refrain.read H Ω O E₀ V₀
variable {e f r s A B M Z : ℝ}
local notation "θ₀"=> P.p.supportExponent
local notation "θ₁"=> P'.p.supportExponent
local notation "p₁"=> P'.p
local notation "θ₂"=> (P'.p.supportExponent+1+1)
variable (W:Walk H P' e f r s)
local notation "ƒ"=> Spire.fees S.ratio.count θ₂
-- Aura recipe at a paid Horizon. D.clock answers EVERY load using Lamp cover; doesn't require model sup beyond `Bright`. `Ready` purchases at post calendar with arbitrary Root/Theta. Select s schedules for real occupancy clocks; budget tolerance in.Scale uses factor 2.
open Lotus
open Trigger Typeface GridRenewal.Rain
variable [DecidableEq V]{R:Marker.Census V}{o:V→Site n}
variable {Y Γ K : ℝ} {k k' : ℕ}
variable (Iris:Eyes H P' e Γ Y K k)
local notation "T"=> Type
-- choose pre-normalizing log-budget* before packing ANY disjoint types/pts. K & Krist input Hit sup T.P0. Can also choose for altered analytic model only.
variable (L0:Gallery α I o P R)(σw:V→ℝ)
variable {b b':ℝ}
variable (U:Seal L0 σw b b')
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
variable [Countable I]
local notation "A*"=> listCosts L0 σw hw hx U.supE U.crown (sighting L0 σw U) U.looks
local notation "z'"=> Trigger.axis L0 σw
variable (hC:∀ u:R.Mode,u.val.card≤k)(hE:2*(b+b')≤K)
local notation "pad'"=> Iris.pad
variable (u:α)
local notation "L★"=> fiscal H (P':=P') Iris L0 σw U hw hx hE u
local notation "Ψ"=> Trigger.choir L0 σw hw k hC

local notation "Θ"=> S.ratio.parent ∘ o
local notation "ρ"=> W.entrance
local notation "Ξ"=> W.offer
local notation "Y0"=> Refrain.read H Ω O W.entrance W.offer
local notation "T!"=> Iris.bells
local notation "ℓ₀"=> Lanes.layoutK H O pad' A* u (fun _ =>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ (Trigger.colorCosting L0 S σw hx · p₁)
local notation "ℓ₁"=> Kiosk.First.led ℓ₀ W.first
local notation "M'"=> Creek.theater H O A* u (fun _=>1) Set.univ 0
local notation "μ"=> Creek.Academy H O A* u (fun _=>1) Set.univ 0 k
local notation "μL"=> Lanes.academy H O pad' A* u (fun _=>1) T! L★ p₁ Iris.block Iris.pole (le_refl _) (le_refl _)
local notation "ƒL"=> QuadraticLocal.Pane.printBulbs Θ M' Set.univ z' μ (Flues.candle A* u S) μL
local notation "w₀"=> Spire.convertGlobal L0.E S p₁
local notation "β"=> (w₀).join ƒL
local notation "H'"=> L0.density
local notation "p0'"=> fun t=> S.push P.beta (TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S)
local notation "early"=> fun t=> S.push P.beta (H' t)
local notation "γ"=> Γ
variable {η ι:Type} [Countable ι][Countable η] (b₀:Canopy.ShiftRows α ι G P'.p (S.ratio.parent ∘ o) R)
   (K₀:Lamps α η G P'.p (S.ratio.parent ∘ o) R)
variable (hY:∀ U:Config G c,P'.eval U≠0) (hp:P'.eval=S.push P.beta P.eval)
local notation "Ɓ"=> respondent H W Iris L0 σw U hw hx hC hE u b₀ K₀
variable (κ_:ℝ) -- conflicts main κ; rename
variable [Fintype V]
include hY hp U W Iris hE hC
set_option quotPrecheck false
local notation "r₀"=> Stoop.radius σw κ_
-- κ_
set_option maxHeartbeats 200000 in
lemma success_scaled (s':Tree.Forest S.ratio) (hk:1≤κ_) (hB:b₀.Budget (Stoop.radius σw κ_) P'.p.B (P'.p.supportExponent+1) s)
    (hK:K₀.Paid σw P'.p.B P'.p.supportExponent q)(h:∀ t U',(β).log t U'= K₀.log t U'+b₀.log t U'):
    (Ɓ).Pays (r₀) P'.p.supportExponent ((κ_)⁻¹*q) r ∧ (∀ t,S.push P.beta (L0.density t)=(Ɓ).density t) := Function.const _ (by
    let δ := β; have hw':∀ i,0<(r₀) i:= fun i=> div_pos (hw i) (zero_lt_one.trans_le hk); have ht:= Stoop.tighten σw _ hw hk hK; obtain ⟨hδ,hF,hQ⟩:= docket H W Iris L0 σw U hw hx hC hE u s'; obtain ⟨hV,hP⟩:= Kiosk.Second.passes early (β).log ℓ₁ b₀ W.second hw' P'.p.exponent_pos.le (Stoop.leaves σw _ hw hk hF) hB hQ K₀.log h (fun t U=>Lamps.quiet_of_hasSum _ _ (hK.sums P'.p.exponent_pos.le hw ..))
    exact ⟨⟨ht,hV⟩, upkeep _ P' K₀ _ ht P'.p.exponent_pos.le hw' hP (fun t U'=> by rw [hp, tuneQuiet H Iris L0 σw U hw hx hC hE u]) hY⟩
  ) (inferInstance : Countable η)
end Travel
end YM.QuadraticLocal
