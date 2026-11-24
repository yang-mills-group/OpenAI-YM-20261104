import YM.OPE.Compatible.Roan.Stick
/-! # Split contour.Far.Tx tags finite. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n:ℕ}{t C s u z ℓ v a c e r R β:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T} {q:Sender L} (p:Site L.f) (j:Phase) {Y:Studio L}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "μ"=> Y.μφ
local notation "S!"=> Spex L Y q j
local notation "G!"=> FWind G s c u C t
local notation "U!"=> RiseT G k s c u C t z a
abbrev roomV (G:Gauge)(n:ℕ)(z:ℝ):= z*Fintype.card G.ColorIndex+n
local notation "R!"=>roomV G
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0< e)(hv:Scale Y t) {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z) (hX:Training L p X r) (hp: Funded L X q a k)
include h ht hc he hv hx hp hX
local notation "Ε!"=> Βuffs G s c C
lemma nonhome (x:RodZ L n)(hs:∀ i:Fin n, r+ℓ ≤ Dtn p (Wct L (x i))): ‖Wish2 L q Y j x‖ ≤ (U! 2*(reelP G! (Ε! (R! 0 z)) n 2))* Real.exp (-(u*ℓ)):=by
           obtain ⟨J,hJ,H,hK,hσ⟩:=auction L p Y X hX ∅ (fun i hi=> False.elim ((Finset.notMem_empty i) hi)); have hx'(i):= Alien L p Y J _ (hs i) H; have hk:(J.card:ℝ) ≤ roomV G 0 z:=by
                 unfold roomV; push_cast; rw[add_zero]; rw [Finset.card_empty,add_zero] at hJ; apply le_trans ((Nat.cast_le (α:=ℝ)).mpr hJ); rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)
           exact telemetry.swing (Fare L Y J x h ht hc he hv hx' hk) (Fans h ht hc he hv X hx q hp j) (yieldX L Y J hp hK j)
lemma aCross (x:RodZ L n)(y:RodZ L m)(hz:∀ i:Fin n,r+ℓ ≤ Dtn p (Wct L (x i)))(hy:∀ i:Fin m,r+ℓ ≤ Dtn p (Wct L (y i))) :
            ‖Wish3 L q Y j x y‖ ≤ telemetry.Bezel U! (hikeP G! n) (hikeP G! m) (reelP G! (Ε! (R! 0 z)) n) (reelP G! (Ε! (R! 0 z)) m)*Real.exp (-(u*ℓ)):=by
                 obtain ⟨J,hJ,H,hK,hσ⟩:=auction L p Y X hX ∅ (fun i hi=> False.elim ((Finset.notMem_empty i) hi)); have hx'(i):=Alien L p Y J _ (hz i) H; have hy'(i):=Alien L p Y J _ (hy i) H; have hk:(J.card:ℝ) ≤ roomV G 0 z:=by unfold roomV; push_cast; rw[add_zero]; rw [Finset.card_empty,add_zero] at hJ; apply le_trans ((Nat.cast_le (α:=ℝ)).mpr hJ); rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)
                 exact telemetry.Pairing (Fare L Y J x h ht hc he hv hx' hk) (Fans h ht hc he hv X hx q hp j) (yieldX L Y J hp hK j) (Fare L Y J y h ht hc he hv hy' hk)
lemma Thus (x: RodZ L n)(y:RodZ L m)(hz:∀ i:Fin n,r+ℓ ≤ Dtn p (Wct L (x i)))(hy:∀ i:Fin m,Dtn p (Wct L (y i))≤ r): ‖Wish3 L q Y j x y‖≤ telemetry.Garlic U! (hikeP G! m) (reelP G! (Ε! (R! m z)) n)* Real.exp (-(u*ℓ)):=by
          let Q:= Finset.univ.image y; have hh: Q.card≤ m:= Finset.card_image_le.trans_eq (by rw [card_univ,Fintype.card_fin]) ; obtain ⟨J,hJ,H,hK,hσ⟩:= auction L p Y X hX Q (fun i hi=>by obtain ⟨p,h,rfl⟩:=mem_image.mp hi; exact hy p); have hk:(J.card:ℝ) ≤ roomV G m z:=by
              apply le_trans ((Nat.cast_le (α:=ℝ)).mpr (hJ.trans (add_le_add le_rfl hh))); unfold roomV; push_cast; exact add_le_add (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)) le_rfl
          have he' := Broad L Y J y (fun i=>hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))); unfold Wish3; rw[(Order3 Y.μφ _ _ _).1]; exact telemetry.shot (Fare L Y J x h ht hc he hv (fun i=> Alien L p Y J _ (hz i) H) hk) (Fans h ht hc he hv X hx q hp j) (Bsafe L Y y h ht hc he hv) (yieldX L Y J hp hK j) he'
end
end YM.OPE.Borealis.Galea
