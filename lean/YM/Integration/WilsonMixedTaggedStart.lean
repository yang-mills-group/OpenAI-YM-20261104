import YM.Integration.WilsonMixedTaggedBudget
import YM.Integration.WilsonMixedTaggedOutput
import YM.Integration.WilsonAllDateHarvestEndpointIntegrability

/-! Start from the actual represented fine input. The two projections give
the actual and stripped old-gas programs on all fields. The amplified
density is integrable by the genuine original inventory and heat theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedStart
open Finset Function Set MeasureTheory Lattice Wilson RG Marker MergeProof Accent RG05Readout
open RG05Readout.Many Address Push GridApprox.Nil Ac Extra.Histories Extra.Multi
open WilsonMixedTaggedEntries WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
variable {G : Gauge} {n : Side} {R : Rep G n} {o : V → Site n}
variable {w : V → ℝ} {e δ : ℝ}
variable (Φ : V → Config G n → ℂ) (κ : V → Box n → Config G n → ℂ)
variable {H : Support n → Config G n → Poly B} {K : Box n → Config G n → Poly B}
local notation "Bₜ" => census B

def lifted (δ : ℝ) (H : Support n → Config G n → Poly B) (K : Box n → Config G n → Poly B)
    (U : Config G n) : Poly Bₜ :=
  restore R (liveRow Φ) (liveRow κ) (fun i Y=>pack (δ:ℂ)⁻¹ (H i Y))
    (fun i Y=>pack (δ:ℂ)⁻¹ (K i Y)) U

theorem represented (hd : 0 < δ) (h : Carton o H K R.p.threshold)
    (hH : Towed w id H R.p.B e δ) (hK : Towed w Prod.fst K R.p.B e δ) :
    Served R (liveRow Φ) (liveRow κ) (lifted (R:=R) Φ κ δ H K)
      (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 :=
  ⟨_,_,WilsonMixedTaggedEntries.carton _ h,WilsonMixedTaggedBudget.unit hd hH,
    WilsonMixedTaggedBudget.unit hd hK,rfl⟩

theorem projected (z : ℂ) (h : Carton o H K R.p.threshold) (U : Config G n) :
    specialize B z (lifted (R:=R) Φ κ δ H K U) = restore R Φ κ
      (fun i Y=>(z * (δ:ℂ)⁻¹) • H i Y) (fun i Y=>(z * (δ:ℂ)⁻¹) • K i Y) U := by
  unfold lifted
  rw [restoration z Φ κ (WilsonMixedTaggedEntries.carton _ h) U]
  have hE i Y : specialize B z (pack (δ:ℂ)⁻¹ (H i Y)) =
      (z * (δ:ℂ)⁻¹) • H i Y := unpack ((h.exp i).1.sil Y) _ _
  have hF i Y : specialize B z (pack (δ:ℂ)⁻¹ (K i Y)) =
      (z * (δ:ℂ)⁻¹) • K i Y := unpack (hop B _ ((h.flag i).2 Y)) _ _
  simp_rw [hE,hF]

theorem endpoints (hd : 0 < δ) (h : Carton o H K R.p.threshold) (U : Config G n) :
    specialize B (δ:ℂ) (lifted (R:=R) Φ κ δ H K U) = restore R Φ κ H K U ∧ 
    specialize B 0 (lifted (R:=R) Φ κ δ H K U) = restore R Φ κ 0 0 U := by
  have hne : (δ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  constructor
  · simpa only [mul_inv_cancel₀ hne,one_smul] using projected (δ:=δ) Φ κ (δ:ℂ) h U
  · have zH : (0:Support n → Config G n → Poly B) = fun _ _=>(0:Poly B) := by
      funext i Y
      rfl
    have zK : (0:Box n → Config G n → Poly B) = fun _ _=>(0:Poly B) := by
      funext i Y
      rfl
    rw [zH,zK]
    simpa only [zero_mul,zero_smul] using projected (δ:=δ) Φ κ 0 h U

end YM.Integration.WilsonMixedTaggedStart
