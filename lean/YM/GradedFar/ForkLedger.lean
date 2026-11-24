import YM.GradedFar.Stratum
import YM.GradedFar.Orbit
/-!
# Price all uses of the new physical packet (at fixed physical labels)

Any finite Near roster, even empty; below adapt physical positions/horizon accordingly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I:Type} [Fintype I] (d:I→ℕ) (h j:ℕ)
variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {M δ:ℝ} (hm:0≤M)(hd:0<δ)
local notation "Λ" => Labels S d
local notation "Spend" => Sold (𝓝[>](0:ℝ))
def LedgerR (h:ℕ) (i:Launch I) := packetCost (d:=d) F i.x i.center h Q - view_shadow F i.x i.center h Q.port

def LedgerC (a:Q.channels j) (i:Launch I) :=
  (Cast.judge F Q ⟨Fin.last j,a⟩).compMultilinearMap (packetCost (d:=d) F i.x i.center j Q)

lemma settlePacket (i:Launch I)(u:Λ): LedgerR F d Q h i u = Q.packet h i.x u i.center-shadowOld Q.port h i.x i.center u:=by
  rw [LedgerR,_root_.sub_apply, packetCost_apply, view_shadow_apply]
lemma settleCoef (a:Q.channels j) (i:Launch I)(u:Λ): LedgerC F d j Q a i u = Q.coef j a i.x u i.center:=by
  rw [LedgerC,LinearMap.compMultilinearMap_apply, packetCost_apply, Cast.packet_judged]; rfl

variable (bank:LogTrace F Q.port)
include bank hm hd
lemma CostedC (a:Q.channels j)(u : Λ) : Spend (Tiny M δ) TagCost (fun r (_:Launch I)=>r^j/r^(∑i,d i)) (fun _ (i:Launch I)=>
    Q.coef j a i.x u i.center) := by
  apply (fixed (Cast.judge F Q ⟨Fin.last j,a⟩).toContinuousLinearMap
    (fresh_price_good F d j Q hm hd bank u)).congr; intro _ i
  apply congrArg ((Q.basis j).coord a)
  exact Subtype.ext (Q.test_fixes j _ (Q.fresh_mem j _ _ _))

lemma CostedR : ∀ u:Λ, Spend (Tiny M δ) TagCost (wage d h) (fun _ (i:Launch I)=> LedgerR F d Q h i u) := fun u=>
  (packet_pose F d h Q hm hd u bank).congr (fun _ _=> (settlePacket ..).symm)

variable (L:ℝ)(hL:0≤L)
include hL
theorem G7_price : ∃ k:ℕ, ∃ b:ℝ, 0≤b ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ o x, WithinRoom r M δ x o →
    ∀ (a:Q.channels j) (u:Λ), (∀ i,‖u i‖≤L) → ‖Q.coef j a x u o‖ ≤ b*badge r^k*(r^j/r^(∑i,d i)) := by
  have H (a:Q.channels j):= Sold.wallet (A:=fun _ i=> LedgerC F d j Q a i) (fun u:Λ=>
    (CostedC F d j Q hm hd bank a u).congr (fun _ i=> (settleCoef ..).symm)) (compact_pay ..) L hL
  obtain ⟨k,h⟩:=(eventually_all.mpr H).exists; obtain ⟨b,hb,hQ⟩:= ((eventually_ge_atTop 0).and (eventually_all.mpr h)).exists
  refine ⟨k,b,hb,(eventually_all.mpr hQ).mono ?_⟩
  intro r h o x hx a u hu; specialize h a (⟨x,o⟩:Launch I) hx u hu; rw [settleCoef] at h; exact h

theorem G5_price : ∃ k:ℕ, ∃ b:ℝ, 0≤b ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ o x, WithinRoom r M δ x o →
    ∀ u:Λ, (∀ i,‖u i‖≤L) → ‖Q.fresh j x o u-Q.cutTest j h (shadowOld Q.port h x o u)‖ ≤ b*badge r^k*(r^(h+1)/r^(∑i,d i)) := by
  let A (i:Launch I):= Q.fresh j i.x i.center (d:=d)-(Q.cutTest j h).compMultilinearMap (view_shadow F i.x i.center h Q.port)
  have h₀(z) (u:Λ): A z u= Q.fresh j z.x z.center u-Q.cutTest j h (shadowOld Q.port h z.x z.center u):= by
    dsimp only [A]
    rw [_root_.sub_apply,LinearMap.compMultilinearMap_apply, view_shadow_apply]
  obtain ⟨k,h⟩:= (Sold.wallet (A:=fun _ z=>A z) (fun u=> (bridge_poses F d h j Q hm hd u bank).congr
    (fun _ i=> (h₀ i u).symm)) (wage_ok d h _) L hL).exists
  obtain ⟨b,hb,hQ⟩:= ((eventually_ge_atTop 0).and h).exists
  exact ⟨k,b,hb,hQ.mono (fun r hr o x hx u hu=> (h₀ (⟨x,o⟩:Launch I) u).symm ▸ hr _ hx u hu)⟩

theorem G8_price : ∃ k:ℕ, ∃ b:ℝ, 0≤b ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ o x, WithinRoom r M δ x o →
    ∀ u:Λ, (∀ i,‖u i‖≤L) → ‖Q.packet h x u o-shadowOld Q.port h x o u‖ ≤ b*badge r^k*(r^(h+1)/r^(∑i,d i)) := by
  obtain ⟨k,hQ⟩:= (Sold.wallet (CostedR F d h Q hm hd bank) (wage_ok d h _) L hL).exists
  obtain ⟨b,hb,hQ⟩:= ((eventually_ge_atTop 0).and hQ).exists; refine ⟨k,b,hb,hQ.mono ?_⟩
  intro r Hr o x hx u hu; specialize Hr (⟨x,o⟩:Launch I) hx u hu; rw [settlePacket] at Hr; exact Hr
end YM.Integration.GradedFar.Fork
