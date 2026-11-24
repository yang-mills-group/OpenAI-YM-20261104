import YM.GradedFar.Cancel
import YM.GradedFar.Arithmetic

/-!
# The paid remainder after cropping

Throughout, `s` is log T, **not** the coupling.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

section budget
variable {I : Type} {p : ℕ} {a : ℝ} {F Q : I → ℝ → PowerSeries ℂ} (t : I → ℝ) (ht : ∀ i, |t i| ≤ 1)
include ht
lemma pay_power (k : ℕ) : Rain 0 (fun (i : I) (_ : ℝ) => (t i:ℂ)^k) := by
  refine Rain.powers (Rain.cash ⟨1,?_⟩) k; intro i; rw [Complex.norm_real, Real.norm_eq_abs]; exact ht i
lemma charge_crop (h : ChargeP (p+1) a F) : Rain a (fun i s => crop p (t i) (F i s)) := by
  simp only [crop_eq]
  refine Rain.sum _ fun q hq => ?_
  exact Rain.cover (pay_power t ht q) (h q (Finset.mem_range.mp hq))
lemma charge_invoice (h : ChargeP (p+1) 0 F) (hy : ChargeP (p+1) a Q) :
    Rain a (fun i s => invoice p (t i) (F i s) (Q i s)) := by
  unfold invoice
  refine Rain.sum _ fun q hq => Rain.cover (pay_power t ht _) ?_
  obtain ⟨⟨hj,hk⟩,_⟩ := (mem_pairsAbove p q).mp hq
  exact Rain.cover (h _ (by omega)) (hy _ (by omega))
end budget

variable {G : Gauge} {n m h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} {N : WilsonPrescription G}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)

/-- `[Dˣ]crop c` uses `[Dˣ]crop` as a linear map on output sectors.
This proves the separately cropped recipe takes exactly that form, on each row. -/
lemma charged_identity (p h : ℕ) (x : Points n) (y : Points m) (u : Inputs G d)
    (v : Inputs G e) (t s : ℝ) :
    crop p t (Dx N T y v s (cActual N x u h p t)) =
      ∑ q : Toon G h, crop p t (seriesComponent N x u (flash q)) * crop p t (DX N T q y v s) := by
  unfold Dx responses
  rw [crop_sum]; simp_rw [crop_C_mul,coord_actual]; rfl

section
variable {K : Set (Points n)} {S : Set (Points m)}
variable (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
variable (e d) (L R : ℝ) (p h : ℕ)

include H hK hx hS hy
/-- Internal form at large log-distance. `hf` price in this proof includes powers 0,...,p of both
series. Exponents chosen *before* the coupling, fields and positions.

Enough to pay the final price to assume `|t|≤1` and `|t|≤2*g` (latter in absolute
value, no direction-of-running/even-odd trick). See `Measured` below for this input
on the actual read of the coupling and its hypothesis.
-/
theorem bound_log : ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, ∀ᶠ s in atTop,
    ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
    ∀ x ∈ K, ∀ y ∈ S, ∀ t g : ℝ, |t| ≤ 1 → |t| ≤ 2*g →
      ‖crop p t (Yx N T x y u v s) - crop p t (Dx N T y v s (cActual N x u h p t))‖ ≤
        D * ( (exp s)⁻¹^(h+1) + g^(p+1)) * (1+s)^a := by
  let I := ↥K × ↥S × {u : Inputs G d // Within L u} × {v : Inputs G e // Within R v} × {t : ℝ // |t| ≤ 1}
  let x (i : I) : ↥K := i.1
  let y (i : I) : ↥S := i.2.1
  let u (i : I) := i.2.2.1.val; let v (i : I) := i.2.2.2.1.val; let t (i : I) := i.2.2.2.2.val
  have hu (i : I) : Within L (u i) := i.2.2.1.property
  have hv (i : I) : Within R (v i) := i.2.2.2.1.property
  have ht (i : I) : |t i| ≤ 1 := i.2.2.2.2.property
  let F i s := Yx N T (x i).val (y i).val (u i) (v i) s
  let C (q : Toon G h) i := seriesComponent N (x i).val (u i) (flash q)
  let Q (q : Toon G h) i s := DX N T q (y i).val (v i) s
  let core i s := crop p (t i) (F i s - ∑ q, C q i * Q q i s)
  let extra i s := ∑ q, invoice p (t i) (C q i) (Q q i s)
  have hf : Rain ((h:ℝ)+1) core := charge_crop t ht
    (charge_basket H hK hx hS hy u v x y p hu hv h) -- plus charge_Y prices available
  have hc (q : Toon G h) : ChargeP (p+1) 0 (fun i _ => C q i) :=
    fun k _ => Rain.cash (price_components H hK hx u x k hu (flash q))
  have hre : Rain 0 extra := Rain.sum _ fun q _ => charge_invoice t ht (hc q)
    ((charge_center H hS hy v y p hv q).grow (Nat.cast_nonneg _))
  obtain ⟨D,hD,a,hr⟩ := hf; obtain ⟨B,hB,b,hV⟩ := hre
  refine ⟨D+2^(p+1)*B, by positivity,a+b,?_⟩
  filter_upwards [hr,hV,eventually_ge_atTop (0:ℝ)] with s hs hcost hs0
  intro U hU V hV X hX Y hY w g hw hG
  let i : I := (⟨X,hX⟩,⟨Y,hY⟩,⟨U,hU⟩,⟨V,hV⟩,⟨w,hw⟩)
  rw [charged_identity]; change ‖crop p (t i) (F i s) - ∑ q, crop p (t i) (C q i) * crop p (t i) (Q q i s)‖ ≤ _
  have W := hs i; have W' := hcost i
  have hp : crop p (t i) (F i s) - ∑ q, crop p (t i) (C q i) * crop p (t i) (Q q i s) =
        core i s - (t i:ℂ)^(p+1)*extra i s := by
    simp_rw [core,crop_sub,crop_sum, extra, crop_invoice,Finset.sum_add_distrib, Finset.mul_sum]
    abel
  rw [hp]
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply (add_le_add W (mul_le_mul (show |t i|^(p+1) ≤ (2*g)^(p+1) from
    pow_le_pow_left₀ (abs_nonneg _) hG _) W' (norm_nonneg _) (by have : 0 ≤ 2*g := (abs_nonneg _).trans hG; positivity))).trans
  have h0 : 0 ≤ g := by have hh := (abs_nonneg w).trans hG; linarith only [hh]
  exact collect D B s g a b h p hs0 h0 hD hB
end
end
end YM.FVA2.GradedFar
