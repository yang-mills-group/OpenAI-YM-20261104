import YM.MS.Rake.Hour
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Rake/Hour.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake.Geo
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {I J:Type}{G: Gauge}{b c:Bool}{x:I→QP}(P: Geo I){K L:Planet G I}{F H: Glade G I}
local notation "Ψ"=> east P b
variable (h:Stage K L P b)
include h
variable {P}
structure WCoverSep (P:Geo I)(x:I→QP) : Prop where
    full: ∃ C:ℝ,0<C∧∃ j : ℕ, ∀ i, ‖x i‖ ≤ C * P.habitat i^j * P.roots i
    floor: ∃ C:ℝ,0<C∧∀ i,C*P.roots i≤‖x i‖

omit h in
/-- The polynomial in the upper bound is paid in this *same profile's* market.
Works for all three clocks and with enlargement of the roots factor if required. -/
lemma WCoverSep.pay (hx : WCoverSep P x) (V : Belt I)
    (basic : ∀ i : V.time, V.price.basic i = P.habitat i.1 * (1 + |i.2.val|))
    {q : V.time → ℝ} (cover : ∀ i : V.time, P.roots i.1 ≤ q i) :
    paid V.price (fun i => ‖x i.1‖) q := by
  obtain ⟨D, hD, j, hfull⟩ := hx.full
  refine ⟨D, hD, j, fun i => le_trans (hfull i.1) ?_⟩
  have hh : 0 ≤ P.habitat i.1 := by unfold habitat; positivity
  have hb : P.habitat i.1 ≤ V.price.basic i := by
    rw [basic]
    exact le_mul_of_one_le_right hh (by simp)
  have hj : D * (P.habitat i.1)^j ≤ D * (V.price.basic i)^j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hb j) hD.le
  exact mul_le_mul hj (cover i) (exp_pos _).le
    (mul_nonneg hD.le (pow_nonneg (hh.trans hb) _))

lemma touch_wide (hz: WCoverSep P x){n m:ℕ}(he: Tip P b false n F)(hx:Tip P b false m H): Came P b ( fun i t=> Cabin (x i) ( L i t ) planeF ( F i t ) ( H i t )):= by
    refine ⟨⟨?_, warmJoin (fun _=>Coherent) h.pool he.2.1 hx.2.1⟩, collect_join _ L he.1 hx.1⟩; intro k; obtain ⟨l,hM⟩:= money (b:=b) ( P:=P ) k n m; obtain ⟨C,hC,H⟩:=hz.floor; refine Lease.sticks ( PulseQ ( v:=fun i=>P.roots i.1 ) ( A:=x∘ Sigma.fst ) h.well he.2.2 hx.2.2 ( airLamp _ _ ) (rateC _ _ ) (rateC _ _ ) (fun _=>exp_pos _) (fun i=> (H i.1)) ( rightB P ) (hz.pay (east P b) (fun _ => rfl) (fun _ => le_rfl)) hC l ) hM
end YM.MS.Rake.Geo
