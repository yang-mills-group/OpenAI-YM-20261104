import YM.GradedFar.Joint
import YM.GradedFar.Consistent

/-!
# Entry for *the formal side only*. Read large physical corpus only if needed for the client.

How to consume with the assumptions of the supplied paper (NearFarDelta).
Keep H and all choices. On physical side the thermometer `t` is at the posed
frame, *not* repriced Order, *not* the meter in `Match.positionCoupling`. See `Clock`
for pricing it here, `Measured` for working at the actual physical book. This
entry works for **any** such thermometer, doesn't assume H field estimates or any
true OPE estimate.

(Notation `s` here in column APIs is log T; written proof sometimes uses `s` for a
physical radius.)
-/

namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m ℓ : ℕ} {N : WilsonPrescription G}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {K : Set (Points n)} {S : Set (Points m)}
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
  (d : Fin n → ℕ) (e : Fin m → ℕ)

include H
/-- Read on precisely the original kernel. -/
lemma Yx_configuration (x : Points n) (u : Inputs G d) (y : Points m) (v : Inputs G e) (s : ℝ)
    (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) (hp : forest x (squeeze (-s) y) ∈ conf (n+m)) (j : ℕ) :
    coeff j (Yx N M x y u v s) = ∑ D ∈ Normalize.tally j m,
      Measure.outlook N.scheme N.criterion ℓ _ ⟨forest x (squeeze (-s) y),hp⟩ (D none)
        (Fin.append (installedInputs hd u) (installedInputs he fun i =>
          Level.Dial (e i) (-s) (coeff (D (some i)) (GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1) (-s) (e i)) (v i)))) := by
  unfold Yx
  rw [coeff_applyFar _ _ _ _ _ (H.separatedOPE (Teller.logNu 1)).wilson.dimensions hd he hp]
  unfold emitted exterior
  simp_rw [Kfactor]
lemma Dx_configuration (h : ℕ) (a : Sec G h) (y : Points m) (v : Inputs G e) (s : ℝ)
    (hd : h ≤ ℓ) (he : ∀ i, e i ≤ ℓ) (hp : outgoing (squeeze (-s) y) ∈ conf (1+m)) (j : ℕ) :
    coeff j (Dx N M y v s a) = ∑ D ∈ Normalize.tally j m,
      Measure.outlook N.scheme N.criterion ℓ _ ⟨outgoing (squeeze (-s) y),hp⟩ (D none)
        (Fin.append (fun _ => up hd a) (installedInputs he fun i =>
          Level.Dial (e i) (-s) (coeff (D (some i)) (GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1) (-s) (e i)) (v i)))) := by
  unfold Dx; rw [responses_eq]
  exact Yx_configuration H (fun _ => h) e (0:Points 1) (fun _ => a) y v s (fun _ => hd) he hp j

include hK hx hS hy
/-- The formal theorem (with just the pricing hypotheses on t, from PoseFit F.3);
use even for `T` limited to M.1 range. Below `Bound` supplies the actual configuration-space
clauses for these hypotheses (not off-domain tests). Also see `charge_Y` & `charge_center`
for costs of the ingredients *separately*. Joint test result is simultaneous as well;
e.g., apply `tested` using this very first clause. Proper subarrays (use even the same
`T`) are covered by the same `prices` routine. If reusing the full layout with all units
on vacancies see `Subarray.book_unit`, `column_unit`, `Subarray.Yx_mask`, `responses_eq`,
`Subarray.vector_mask`, `Subarray.empty_c`.
-/
theorem formal_second (t proxy : ℝ → ℝ)
    (hproxy : Tendsto (fun r => proxy r / gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
    (k : ℕ) (hk : 2 ≤ k) (B : ℝ) (hF3 : ∀ᶠ r in 𝓝[>] (0:ℝ), |t r - proxy r| ≤ B * gYM G r ^ k)
    (L R : ℝ) (p h : ℕ) :
    (∀ᶠ r in 𝓝[>] (0:ℝ), 0 < gYM G r ∧ 0 < t r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2*gYM G r) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S,
        ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
          ‖crop p (t r) (Yx N M x y u v (log T)) -
            crop p (t r) (Dx N M y v (log T) (cActual N x u h p (t r)))‖ ≤
            C * (T⁻¹^(h+1) + gYM G r^(p+1)) * (1+log T)^a := by
  have hr := relative_reading simple t proxy hproxy k hk B hF3
  exact ⟨paid_reading simple t hr, paid H hK hx hS hy d e L R p h t hr⟩
end
end YM.FVA2.GradedFar
