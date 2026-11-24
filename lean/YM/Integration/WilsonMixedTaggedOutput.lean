import YM.Integration.WilsonMixedTaggedRoster
import YM.Integration.WilsonMixedTaggedPrice

/-! The output of one finite original multi-source session gives *paired*
regular and forced witnesses for both physical specializations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedOutput
open Finset Function Marker RG05Readout.Many Lattice Wilson RG MergeProof Accent
open MeasureTheory Push GridApprox.Nil Ac Extra.Histories
open WilsonMixedTaggedRoster WilsonMixedTaggedPrice
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side}
variable (B : Census V)
local notation "Bₜ" => census B

def specialize (z : ℂ) : Poly Bₜ →ₐ[ℂ] Poly B := feed (WilsonMixedTaggedPrice.weight Prod.snd z) (project B)

def liveRow {Y : Type*} [Zero Y] (f : V → Y) (v : V × Bool) : Y :=
  if v.2 then 0 else f v.1

theorem sum_live (z : ℂ) (f : V → ℂ) (j : V) :
    (∑ v:V×Bool,if v.1=j then WilsonMixedTaggedPrice.weight Prod.snd z v * liveRow f v else 0) = f j := by
  simp [Fintype.sum_prod_type,WilsonMixedTaggedPrice.weight,liveRow]

variable {B} {R : Rep G n} {o : V → Site n} {w : V → ℝ} {e : ℝ}

/-- Projection of both members of a paired witness leaves old gas,
all singleton profiles, and all covers and disconnected monomials intact. -/
theorem restoration (z : ℂ) (Φ : V → Config G n → ℂ) (κ : V → Box n → Config G n → ℂ)
    {H : Support n → Config G n → Poly Bₜ} {K : Box n → Config G n → Poly Bₜ}
    (h : Carton (o ∘ Prod.fst) H K R.p.threshold) (U : Config G n) :
    specialize B z (restore R (liveRow Φ) (liveRow κ) H K U) =
      restore R Φ κ (fun i V=>specialize B z (H i V))
        (fun i V=>specialize B z (K i V)) U := by
  rw [specialize,carry_restore (project B) (WilsonMixedTaggedPrice.weight Prod.snd z) h]
  congr 2
  · funext i U
    simp [Fintype.sum_prod_type,WilsonMixedTaggedPrice.weight,liveRow]
  · funext i p U
    simp [Fintype.sum_prod_type,WilsonMixedTaggedPrice.weight,liveRow]

theorem original {z : ℂ} (hz : ‖z‖ ≤ 1) (Φ : V → Config G n → ℂ)
    (κ : V → Box n → Config G n → ℂ) {X : Config G n → Poly Bₜ}
    (hw : ∀ v,0 < w v)
    (h : Served R (liveRow Φ) (liveRow κ) X (o ∘ Prod.fst) (w ∘ Prod.fst) e 1) :
    ∃ (H : ℂ → Support n → Config G n → Poly B)
      (K : ℂ → Box n → Config G n → Poly B),
      (∀ u, Carton o (H u) (K u) R.p.threshold ∧ 
        (∀ U,specialize B u (X U)=restore R Φ κ (H u) (K u) U)) ∧ 
      Towed w id (fun i U=>H z i U-H 0 i U) R.p.B e ‖z‖ ∧ 
      Towed w Prod.fst (fun i U=>K z i U-K 0 i U) R.p.B e ‖z‖ := by
  obtain ⟨H,K,box,hH,hK,hX⟩ := h
  refine ⟨fun u i U=>specialize B u (H i U),fun u i U=>specialize B u (K i U),
    fun u=>⟨carry_carton (project B) (WilsonMixedTaggedPrice.weight Prod.snd u) rfl box,fun U=>?_⟩,?_,?_⟩
  · rw [hX]
    exact restoration u Φ κ box U
  · simpa only [specialize,mul_one] using WilsonMixedTaggedPrice.towed (project B)
      Prod.snd hz hH (fun _=>le_rfl) (fun v=>hw v.1) hw
  · simpa only [specialize,mul_one] using WilsonMixedTaggedPrice.towed (project B)
      Prod.snd hz hK (fun _=>le_rfl) (fun v=>hw v.1) hw

end YM.Integration.WilsonMixedTaggedOutput
