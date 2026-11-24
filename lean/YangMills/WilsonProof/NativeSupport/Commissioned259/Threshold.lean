import YangMills.WilsonProof.NativeSupport.Commissioned259.Ball
import YangMills.WilsonProof.NativeSupport.Commissioned259.Crop

/-! # Formal threshold. Combine two DIFFERENT Rain costs in (M.2).

Obtain a T threshold for all |t|≤1 in addition to having g-budget for |t|. Coupling hypothesis
is discharged at application, where one is buying the original construction's *calibrated* t.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m H h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H)
    (he : ∀ i, e i ≤ H) (hh : h ≤ H)
section Algebra
variable (x : Points n) (y : Points m) (η : ℝ) (u : Slots G d) (v : Slots G e) (p : ℕ) (t : ℝ)

lemma remaining :
    crop p t (measurement V B hd he x y η u v) -
      crop p t (center V B he y hh η (purchased V u x h p t) v) =
    crop p t (gap V B hd he hh x y η u v) -
      (t:ℂ)^(p+1)*∑ q : Toon G h, debt p t (farCf V u x (flash q)) (center V B he y hh η (theory q) v) := by
  rw [purchased, reading_linear]; simp_rw [triangle]; rw [Finset.sum_add_distrib,gap,map_sub,map_sum,Finset.mul_sum]; abel
end Algebra
section Threshold
variable {I : Type} {U : ℝ} {K : Set (Points n)} {S : Set (Points m)}
    (hU : 0 ≤ U) (L : Law V R B) (P : O.Canon.Physical V R B)
    (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {x : I → Points n} {y : I → Points m} {u : I → Slots G d} {v : I → Slots G e} {t g : I → ℝ}
    (hx : ∀ i, x i ∈ K) (hz : ∀ i, y i ∈ S)
    (hu : ∀ i, u i ∈ Balls U G d) (hv : ∀ i, v i ∈ Balls U G e) (ht : ∀ i, |t i| ≤ 1)
    (pay : ∀ i, |t i| ≤ 2*g i) (p : ℕ)
include L P hK hc hS hy
section
include hx hz hu hv ht pay hU
lemma threshold : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T : ℝ in atTop, ∀ i,
    ‖crop p (t i) (measurement V B hd he (x i) (T • y i) (-Real.log T) (u i) (v i)) -
      crop p (t i) (center V B he (T • y i) hh (-Real.log T)
        (purchased V (u i) (x i) h p (t i)) (v i))‖ ≤
    C * ((T⁻¹)^(h+1)+(g i)^(p+1))*(1+Real.log T)^a := by
  let D (i:I) (s:ℝ) := ∑ q: Toon G h, debt p (t i) (farCf V (u i) (x i) (flash q))
    (center V B he (squeeze (-s) (y i)) hh (-s) (theory q) (v i))
  have fee : Rain ((h+1:ℕ):ℝ) (fun i s =>
      crop p (t i) (gap V B hd he hh (x i) (squeeze (-s) (y i)) (-s) (u i) (v i))) := by
    push_cast; exact rain_crop p ht (gap_charge hd he hh hU L P hK hc hS hy hu hv hx hz _)
  have cost : Rain ((0:ℕ):ℝ) D := by
    rw [Nat.cast_zero]
    refine Rain.sum _ fun j _ => (rain_debt p ht ?_ (center_charge he hh hU L P hS hy hv hz _ j)).size (Nat.cast_nonneg _)
    intro k _; obtain ⟨M,h⟩ := through_horizon hU P hK hc hu hx (flash j) k
    exact ⟨M, fun i _ => h i⟩
  obtain ⟨M,hM,k,hm⟩ := rain_price_T fee
  obtain ⟨N,hN,l,hn⟩ := rain_price_T cost
  let C := M+(2:ℝ)^(p+1)*N
  refine ⟨C,by unfold C; positivity,k+l,?_⟩
  filter_upwards [hm,hn,eventually_ge_atTop (1:ℝ)] with T hm hn hTone
  intro i
  have hT := zero_lt_one.trans_le hTone
  have hg : 0 ≤ g i := by linarith [pay i, abs_nonneg (t i)]
  have hl : 0 ≤ Real.log T := Real.log_nonneg hTone
  rw [remaining, ← squeeze_T T hT (y i)]
  refine (norm_sub_le ..).trans ((add_le_add (d:=(2:ℝ)^(p+1)*N*(g i)^(p+1)*(1+Real.log T)^l) (hm i) ?_).trans ?_)
  · change ‖(t i:ℂ)^(p+1)*D i (Real.log T)‖ ≤ (2:ℝ)^(p+1)*N*(g i)^(p+1)*(1+Real.log T)^l
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (pay i) _) (hn i) (norm_nonneg _) (by positivity)).trans_eq
    ring
  · calc
    _ ≤ C*(T⁻¹)^(h+1)*(1+Real.log T)^(k+l) + C*(g i)^(p+1)*(1+Real.log T)^(k+l) := by
      gcongr
      · change M ≤ C; unfold C; simp; positivity
      · simp [hl]
      · omega
      · change (2:ℝ)^(p+1)*N ≤ C; dsimp [C]; linarith
      · simp [hl]
      · omega
    _ = _ := by ring
end
include hU
lemma M2_large : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ T : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ∀ t g : ℝ, |t| ≤ 1 → |t| ≤ 2*g →
        ‖crop p t (measurement V B hd he x (T • y) (-Real.log T) u v) -
          crop p t (center V B he (T • y) hh (-Real.log T)
            (purchased V u x h p t) v)‖ ≤ C*((T⁻¹)^(h+1)+g^(p+1))*(1+Real.log T)^a := by
  let Y := {t : ℝ × ℝ // |t.1| ≤ 1 ∧ |t.1| ≤ 2*t.2}
  let I := (↥K × ↥S) × (Balls U G d × Balls U G e) × Y
  obtain ⟨C,hC,a,H⟩ := threshold hd he hh hU L P hK hc hS hy (I:=I)
    (fun i => i.1.1.property) (fun i => i.1.2.property)
    (fun i => i.2.1.1.property) (fun i => i.2.1.2.property)
    (fun i => i.2.2.property.1) (fun i => i.2.2.property.2) p
  exact ⟨C,hC,a,H.mono fun T h x hx y hy u hu v hv t g ht hp =>
    h (((⟨x,hx⟩, ⟨y,hy⟩), (⟨u,hu⟩, ⟨v,hv⟩), ⟨(t,g),ht,hp⟩) : I)⟩
end Threshold
end YM.FVA2.GradedFar259
