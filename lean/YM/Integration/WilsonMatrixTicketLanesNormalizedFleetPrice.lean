import YM.Integration.WilsonMatrixTicketLanesNormalizedFleet

/-! Prices of the joint regular and marked arrays for the original upper roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleetPrice

open OPE Strobe Yarn Vista26 Function Filter Set MeasureTheory Finset Lattice Wilson RG Push
open Marker Source Extra.Histories Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi
open Motion Local Bid Cells Overlay MergeProof Accent Ribbons ManyCopies MergeProof.Float
open PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom Vitrines GridApprox
open Yarn.SitePlan Next.Rank.Station WilsonMatrixTicketLanesNormalizedFleet
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {C : Family G}
variable {W r D} {σ χ : ℕ → ℝ} (H : Tune C W r D σ χ)

include H in
private theorem located {k gap base z j b a t br p N : ℕ} {d : I → ℕ}
    (i₀ : I) {x : I → Site (C.side k p)} (sites : Range26 C k p gap br x i₀)
    (A : ∀ i, Further26 C (d i) j k gap base z b r a t br)
    (roster : Fintype.card I ≤ b) (v : (i:I) → C.label (d i)) (live : k < N)
    (ht : 0 < t) {ρ : ℝ} (pay : ∀ i, Spindle.paid C (d i) k N p (v i) ≤ ρ)
    {w y : I → ℝ} (wp : ∀ i, 0 < w i) (small : ∀ i, w i * ρ ≤ fly C.path.levels (d i) k)
    (yp : ∀ i, 0 < y i) (quote : ∀ i, y i ≤ renal C.path.levels k *
      (near C.path.levels k * w i) * Real.exp ((Loom.count C t k : ℝ)/24)) :
    Measured C base N p k live.le d v ((loops C k p) ∘ x) y := by
  let A₀ := A i₀
  let route := A₀.toPassage
  have hb := A₀.tall.down (C := C) A₀.scroll.le (le_refl _)
  have next := A₀.next
  have reach := A₀.scroll.trans next
  let positions := (royal C base p k).place (fun i => loops C k p (x i) k)
  have apart (v z : Site (C.side base p) × I) (h : v ≠ z) :
      (C.path.levels.budget k).B^8 ≤ separation (positions v) (positions z) := by
    apply corners i₀ sites A₀.gmount hb next.le le_rfl _ v z h
    intro i j hij
    unfold Function.comp
    rw [there, there]
    exact A₀.paid.trans (sites.apart i j hij)
  apply registered H d v ((loops C k p) ∘ x)
    (covers_band i₀ sites A₀.gmount hb roster (living route) route.price next.le)
    (route.tall.hbar.trans reach.le) live (route.notch.trans reach) (fun i => (A i).rank)
    (Habitat i₀ sites A₀.gmount hb roster (next.le.trans live.le))
    (fun b i hi _ => begins (x := x) route hi b) pay wp small yp
  refine Loom.buys (p := Loom.count C t k) (fun _ _ g _ h _ diff => ?_)
    (C.path.levels.budget k).B_pos (Loom.count_pos ht) (fun i => yp i.snd)
    (fun i => mul_pos ((H.brine k).water k le_rfl |>.2)
      (mul_pos ((H.brine k).water k le_rfl |>.1) (wp i.snd)))
    (fun i => quote i.snd)
  simpa only [positions, Function.comp_apply, Loom.stride, Nat.add_sub_cancel] using route.stride.trans (apart g h diff)

include H in
theorem along {A : Type} {φ : Filter A} {k gap : A → ℕ} (L : GracesP C φ k gap)
    (citizen : Citizen C W r D) (d : I → ℕ) (base br : ℕ) (i₀ : I)
    {src weight : A → ℝ} (priced : Coins φ (C.S.scale ∘ k) src)
    (sp : ∀ᶠ i in φ, 0 < src i) (target : Coins φ (C.S.scale ∘ k) weight)
    (wp : ∀ᶠ i in φ, 0 < weight i) :
    ∀ᶠ i in φ, ∀ N p, ∀ live : k i < N, ∀ x : I → Site (C.side (k i) p),
      Sites26 (C := C) br (gap i) x → ∀ v : (s:I) → C.label (d s),
      (∀ s, Spindle.paid C (d s) (k i) N p (v s) ≤ src i) →
      Measured C base N p (k i) live.le d v
        (fun j => loops C (k i) p (x j-x i₀)) (fun _ => weight i) := by
  obtain ⟨z,hz,roll⟩ := ((eventually_gt_atTop (C.ref 0)).and
    (rolls H base (Fintype.card I))).exists
  let w (j:I) (i:A) := fly C.path.levels (d j) (k i) / src i
  have ws j : Coins φ (C.S.scale ∘ k) (w j) :=
    Coins.div (fly_coins (C.S.divergent.comp L.seeks) L.ages (d j)) priced
  have pos j : ∀ᶠ i in φ, 0 < w j i := sp.mono fun i hi =>
    div_pos (H.fog_mono (d j) (le_refl (k i)) |>.1) hi
  have reach : ∀ᶠ t : ℕ in atTop, ∀ j : I, ∀ᶠ i in φ, weight i ≤ renal C.path.levels (k i) *
      (near C.path.levels (k i) * w j i) * Real.exp ((Loom.count C t (k i) : ℝ)/24) :=
    eventually_all.mpr fun j => ruby H L (ws j) target.up (pos j)
  obtain ⟨t,ht,room⟩ := ((eventually_gt_atTop 0).and reach).exists
  filter_upwards [sp,wp,eventually_all.mpr (fun j => room_too H br L citizen (d j) t roll hz),
    eventually_all.mpr room] with i hi hy apparatus arrival N p live x sites v fee
  let relative j := x j - x i₀
  have centered : Range26 C (k i) p (gap i) br relative i₀ := by
    refine ⟨sub_self _, fun j => ?_, fun s j diff => ?_⟩
    · exact (Loom.separation_alt (x j) (x i₀)) ▸ sites.close j i₀
    · simpa [relative,sub_eq_add_neg] using sites.apart s j diff
  exact located H i₀ centered apparatus le_rfl v live ht fee
    (fun j => div_pos (H.fog_mono (d j) (le_refl (k i)) |>.1) hi)
    (fun j => (div_mul_cancel₀ _ hi.ne').le)
    (fun _ => hy) arrival

theorem purchased (simple : G.Simple) (makes : C.Makes) (citizen : Citizen C W r D)
    (d : I → ℕ) (base br e t q : ℕ) (i₀ : I) :
    ∀ᶠ k : ℕ in atTop, ∀ gap : ℕ, (C.path.levels.budget k).B^8 ≤ gap →
    (gap : ℝ) ≤ C.path.levels.clock.hatBeta k^e → ∀ N p, ∀ live : k < N,
    ∀ x : I → Site (C.side k p), Sites26 (C := C) br gap x →
    ∀ v : (j:I) → C.label (d j), (∀ j, Spindle.paid C (d j) k N p (v j) ≤
      C.path.levels.clock.hatBeta k^t) →
    Measured C base N p k live.le d v (fun j => loops C k p (x j-x i₀))
      (fun _ => C.path.levels.clock.hatBeta k^q) := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper makes simple
  let K : ℕ × ℕ → ℕ := Prod.fst
  let n : ℕ × ℕ → ℕ := Prod.snd
  let B := C.path.levels.clock.hatBeta
  let region : Set (ℕ × ℕ) := {i | (C.path.levels.budget (K i)).B^8 ≤ n i ∧
    (n i : ℝ) ≤ B (K i)^e}
  let μ := Filter.comap K atTop ⊓ Filter.principal region
  have late : Tendsto K μ atTop := tendsto_iff_comap.mpr inf_le_left
  have hr : ∀ᶠ i in μ, i ∈ region := Filter.Eventually.filter_mono
    (show μ ≤ Filter.principal region from inf_le_right) (eventually_principal.mpr fun _ h => h)
  have hw : Height C.S μ (C.S.scale ∘ K) K 1 :=
    ⟨late, (tendsto_const_nhds (x := (1:ℝ))).congr' <|
      ((C.S.divergent.comp late).eventually_gt_atTop 0).mono
        (fun i hi => (div_self (a := C.S.scale (K i)) (ne_of_gt hi)).symm)⟩
  have hz := C.S.divergent.comp late
  have hp := hat_price hz hw
  have powers (a : ℕ) : Coins μ (C.S.scale ∘ K) (fun i => B (K i)^a) :=
    Coins.power hp hz _
  have positive (i a : ℕ) : 0 < B i^a :=
    pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed _)) _
  have sale := along H (show GracesP C μ K n from ⟨late,
    (Cheap.power hp.up hz e).norm_le (hr.mono fun i (hi : i ∈ region) =>
      (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),
    hr.mono fun i (hi : i ∈ region) => hi.1⟩) citizen d base br i₀
    (powers t) (Eventually.of_forall fun i => positive (K i) _)
    (powers q) (Eventually.of_forall fun i => positive (K i) _)
  rw [Filter.eventually_inf_principal] at sale
  obtain ⟨u,hu,useDay⟩ := sale
  filter_upwards [hu] with k hk g lo hi
  exact useDay (show (k,g) ∈ K ⁻¹' u from hk) ⟨lo,hi⟩


end YM.Integration.WilsonMatrixTicketLanesNormalizedFleetPrice
end
