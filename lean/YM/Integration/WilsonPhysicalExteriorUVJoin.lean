import YM.Integration.WilsonPhysicalExteriorMixedKernel

/-! The signed covariance and two marked-field errors of the deposited
Wilson/MS ultraviolet join, evaluated on its actual two subword origins. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorUVJoin
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane
open scoped Topology ContDiff Classical
variable {I : Type} {G : Gauge} {S : Belt I} {P : Geo I} {ξ : I → QP}
variable {K L : Planet G I} {F H X Y : Glade G I} {a b c w : S.time → ℝ}

private theorem ratio {l r d T : ℝ} (hl : 0<l) (hr : 0<r) (hT : 0≤T)
    (hd : r≤T*d) (k : ℕ) : (l/max l d)^k ≤ (l/r)^k*T^k := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (div_nonneg hl.le (hl.le.trans (le_max_left ..)))
  apply (div_le_iff₀ (hl.trans_le (le_max_left ..))).mpr
  calc
    l = (l/r)*r := (div_mul_cancel₀ l hr.ne').symm
    _ ≤ (l/r)*(T*max l d) := mul_le_mul_of_nonneg_left
      (hd.trans (mul_le_mul_of_nonneg_left (le_max_right ..) hT)) (div_nonneg hl.le hr.le)
    _ = _ := by ring

/-- All three terms in the actual signed finite-cover subtraction enter
with the same gain at every integration time and at the actual pair positions. -/
theorem difference (hk : Flow S K 1) (hKL : Flow S (K-L) w)
    (hF : Here false true S F b) (hH : Here false true S H b)
    (hFH : Here false true S (F-H) (w*b)) (hY : Here false true S Y c)
    (hXY : Here false true S (X-Y) (w*c))
    (mh : Warm H false) (mf : Warm F false) (mx : Warm X false) (my : Warm Y false)
    (kB : BackF K) (lB : BackF L) (hw : nn w) (hb : nn b) (hc : nn c) (j : ℕ) :
    Here false false S
      (regionC (fun _ => planeF) ξ K F X-regionC (fun _ => planeF) ξ L H Y)
      (fun p=>w p*(b p*c p)*(S.price.length p/max (S.price.length p) ‖ξ p.1‖)^j) := by
  apply parkD hF hH hFH hY hXY mh mf mx my kB lB (fun _=>Coherent)
  · intro A B h₁ h₂
    apply Lease.sticks (WilsonPhysicalExteriorMixedKernel.kernel S.price (fun p=>ξ p.1)
      hk h₁ h₂ (fun _=>zero_le_one) hb (joy hw hc) j)
    intro p; simp only [Pi.one_apply,Pi.mul_apply]; exact le_of_eq (by ring)
  · intro A B h₁ h₂
    apply Lease.sticks (WilsonPhysicalExteriorMixedKernel.kernel S.price (fun p=>ξ p.1)
      hk h₁ h₂ (fun _=>zero_le_one) (joy hw hb) hc j)
    intro p; simp only [Pi.one_apply,Pi.mul_apply]; exact le_of_eq (by ring)
  · intro A B h₁ h₂
    exact WilsonPhysicalExteriorMixedKernel.kernel S.price (fun p=>ξ p.1) hKL h₁ h₂ hw hb hc j

/-- Each true join in the two original UV encodings.  A minimum of roots/T
between the actual pair is sufficient, with an explicit power of T. -/
theorem early {K L : Planet G I} {b : Bool} {n m : ℕ}
    (h : Stage K L P b) (he : Tip P b false n F) (hm : Tip P b false m H)
    (T : I → ℝ) (hT : ∀ i,0≤T i)
    (hs : ∀ i,P.roots i ≤ T i*‖ξ i‖) (k : ℕ) :
    ∃ q : ℕ, Here false false (east P b) (regionC (fun _=>planeF) ξ L F H)
      (fun p=>birthTar P k p*(T p.1)^q) := by
  obtain ⟨q,hq⟩ := money (P:=P) (b:=b) k n m
  refine ⟨q,Lease.sticks (WilsonPhysicalExteriorMixedKernel.kernel (east P b).price
    (fun p=>ξ p.1) h.well he.2.2 hm.2.2 (airLamp _ _) (rateC _ _) (rateC _ _) q) ?_⟩
  intro p
  exact (mul_le_mul_of_nonneg_left
    (ratio ((east P b).price.pos p) (exp_pos _) (hT p.1) (hs p.1) q)
    (mul_nonneg (airLamp _ _ p) (mul_nonneg (rateC _ _ p) (rateC _ _ p)))).trans
    (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hq p) (pow_nonneg (hT _) _))

private lemma tariff (d r k : ℕ) (p : Stem P) :
    chips (Gulf P) p*(rateS (Gulf P) d p*rateS (Gulf P) r p)*
      ((Gulf P).price.length p/P.roots p.1)^k = alt P (d+r) k p := by
  calc
    _ = chips (Gulf P) p*((life P d 0 0 p*life P r 0 0 p)*
        ((Gulf P).price.length p/P.roots p.1)^k) := by rw [dotzero,dotzero]; ring
    _ = chips (Gulf P) p*(life P (d+r) 0 0 p*((Gulf P).price.length p/P.roots p.1)^k) := by
      rw [roll]; simp
    _ = chips (Gulf P) p*life P (d+r) k 0 p := by
      simpa using congrArg (fun t : ℝ => chips (Gulf P) p*t) (stock (P:=P) (h:=d+r) (x:=0) 0 k p).symm
    _ = _ := (congr_fun (alter P (d+r) k) p).symm

/-- The charged signed regulator error on the complete native middle-time
interval. The mass dimension, actual chips gain, and the order of the
requested spatial decay are unchanged. -/
theorem signed {d r : ℕ} (hk : Flow (Gulf P) K 1) (hKL : Flow (Gulf P) (K-L) (chips (Gulf P)))
    (hF : Here false true (Gulf P) F (rateS (Gulf P) d))
    (hH : Here false true (Gulf P) H (rateS (Gulf P) d))
    (hFH : Here false true (Gulf P) (F-H) (chips (Gulf P)*rateS (Gulf P) d))
    (hY : Here false true (Gulf P) Y (rateS (Gulf P) r))
    (hXY : Here false true (Gulf P) (X-Y) (chips (Gulf P)*rateS (Gulf P) r))
    (mh : Warm H false) (mf : Warm F false) (mx : Warm X false) (my : Warm Y false)
    (kB : BackF K) (lB : BackF L) (T : I→ℝ) (hT : ∀ i,0≤T i)
    (hs : ∀ i,P.roots i ≤ T i*‖ξ i‖) (k : ℕ) :
    Here false false (Gulf P)
      (regionC (fun _=>planeF) ξ K F X-regionC (fun _=>planeF) ξ L H Y)
      (fun p=>alt P (d+r) k p*(T p.1)^k) := by
  apply Lease.sticks (difference (ξ:=ξ) hk hKL hF hH hFH hY hXY mh mf mx my kB lB
    cul (rateC _ _) (rateC _ _) k)
  intro p
  exact (mul_le_mul_of_nonneg_left
    (ratio ((Gulf P).price.pos p) (exp_pos _) (hT p.1) (hs p.1) k)
    (mul_nonneg (cul p) (mul_nonneg (rateC _ _ p) (rateC _ _ p)))).trans
    (by rw [← mul_assoc,tariff])

end YM.Integration.WilsonPhysicalExteriorUVJoin
