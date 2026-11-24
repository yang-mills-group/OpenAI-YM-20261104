import YM.Integration.WilsonFiniteVacuumWindingReset
import YM.Integration.WilsonCommonDepositedWinding

/-! On an already interacting Wilson history the first return of every registered
marked subword retains its paired finite and cover tensors. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteDepositedMarkedRows
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D k : ι → ℕ} {I : ι → Type} [∀ i, Fintype (I i)] {e m a r : ℕ}

theorem first (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (X : ∀ i, I i → Seed G (D i)) (w : Gear G → ℝ) (hw : ∀ B, 0 < w B)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (K : ι → ℕ)
    (Z S : Finset ι) (hS : S ⊆ Z) (ha : a ≤ e) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ V : ℝ, 1 ≤ V →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) s V →
      let Y := Gears Q.draws Q.paid K k N (m+1) m (independent X)
      ∀ (n : Side) (p : ι → Cover), MarkU p S ((Y p S).1 n a r) ((Y p S).2 a r) σ (C*V^d) := by
  let P := loose Q.draws m
  let h := (Q.mint (m+1) (by omega)).σ
  have hh : 0 < h := (Q.mint (m+1) (by omega)).width
  let t := min s h
  have ht : 0 < t := lt_min hs hh
  let A := diamond G e (mass k Z) h * OriginalIssuedMarkedRows.fee (k:=k) X Q hm w
  have hf := (preblock X (k:=k) (fun _ => 0) Z e
    (w:=4 * max (w (Q.mint m hm).gear) h)
    (mul_pos (by norm_num) ((hw _).trans_le (le_max_left ..))) hX).1
  have hA : 0 ≤ A := mul_nonneg (zero_le_one.trans (diamond_nn G hh)) hf
  have small : (holt Q m hm t ht).s ≤ (holt Q m hm h hh).s := by
    change min (t/32) _ ≤ min (h/32) _
    exact min_le_min (div_le_div_of_nonneg_right (min_le_right ..) (by norm_num)) le_rfl
  obtain ⟨F,hF,quiet⟩ := WilsonFiniteVacuumWindingDate.prepare Q hm ht
  obtain ⟨W,hW,reset⟩ := WilsonFiniteVacuumWindingReset.rim Q hm ha r
  obtain ⟨d,C,σ,hC,hσ,step⟩ := WilsonFiniteIncomingMarkedWinding.original
    (D:=D) (k:=k) (r:=r) Q hm hS ha ht
  let b := C*F^d*A^S.card*W
  let rent := scalesK P K S * ∑ _ : backRow P.L S, b
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have fee : 0 ≤ rent := mul_nonneg (scalesBound P K S) (Finset.sum_nonneg fun _ _ => hb)
  refine ⟨d,rent,σ,fee,hσ,?_⟩
  intro N cut V hV paid Y n p
  change MarkU p S ((Gears Q.draws Q.paid K k N (m+1) m (independent X) p S).1 n a r)
    ((Gears Q.draws Q.paid K k N (m+1) m (independent X) p S).2 a r) _ _
  rw [gearUp _ _ _ (Nat.lt_succ_self m),gearTop]
  have ledger : scalesK P K S * ∑ _ : backRow P.L S, b*V^d = rent*V^d := by
    rw [←Finset.sum_mul]; exact (mul_assoc ..).symm
  rw [←ledger]
  apply WilsonDepositedRegisteredWinding.addressed P K (fun x => logO Q.draws Q.paid m N (independent X x) k)
    p S n a r σ (fun _ => b*V^d)
  intro j
  let cell := inflate P S j
  let x := chartIn P p cell
  have marked := WilsonRegisteredBareMarkedWinding.registered Q hm cut X w hw Z (fun _ => cell) hX p n
  have previous : WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) t V :=
    fun n a lo hi l rank => (paid n a lo hi l rank).mono (min_le_left ..)
  have row := step N cut n (independent X x) p cell (IndependentSourcePathFamily.empty X x)
    (legal X x hX) (F*V) A (one_le_mul_of_one_le_of_one_le hF hV) hA
    (quiet N cut n V hV previous) (fun S hS a ha l => (marked S hS a ha l).mono small)
  apply row.more
  have enough := mul_le_mul_of_nonneg_left (reset N cut)
    (show 0 ≤ C*(F*V)^d*A^S.card by positivity)
  exact enough.trans_eq (by unfold b; rw [mul_pow]; ring)

theorem original (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (X : ∀ i, I i → Seed G (D i)) (w : Gear G → ℝ) (hw : ∀ B, 0 < w B)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (K : ι → ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ V : ℝ, 1 ≤ V →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) s V →
      let Y := Gears Q.draws Q.paid K k N (m+1) m (independent X)
      ∀ (n : Side) (p : ι → Cover) (S : Finset ι) (j : ℕ), j ≤ e → ∀ l,
        MarkU p S ((Y p S).1 n j l) ((Y p S).2 j l) σ ((C*V^d)^S.card) := by
  classical
  let T := Finset ι × Fin (e+1) × Fin (mass k Finset.univ+e+1)
  choose f C u fees hot row using fun b : T => first (r:=b.2.2.val) Q hm X w hw hX K
    Finset.univ b.1 (subset_univ _) (Nat.lt_succ_iff.mp b.2.1.isLt) hs
  obtain ⟨σ,A,d,hσ,hA,room⟩ := WilsonFiniteVacuumWindingReset.common u C f hot fees
  refine ⟨d,A,σ,hA,hσ,?_⟩
  intro N cut V hV prior Y n p S a ha l
  have well := (OriginalCoverReanchoring.iterated (k:=k) X Q.draws Q.paid K
    (j:=m) (b:=m+1) (N:=N) (Nat.le_succ m) cut Q.hG Q.green hX).1
  have one : 1 ≤ A*V^d := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hV)
  have enough := pow_nonneg (zero_le_one.trans one) S.card
  by_cases empty : S = ∅
  · subst S
    rw [show Y p ∅ = 0 from well.quiet' p]
    exact MarkU.zero.more enough
  by_cases legal : l < mass k Finset.univ+e+1
  · let b : T := (S,⟨a,Nat.lt_succ_iff.mpr ha⟩,⟨l,legal⟩)
    have cost := (room b).2 V hV
    have live := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    exact ((row b N cut V hV prior n p).mono (room b).1).more
      (cost.trans (le_self_pow₀ one (Nat.ne_of_gt live)))
  · have hmS : mass k S ≤ mass k Finset.univ := by
      unfold mass; exact Finset.sum_le_sum_of_subset (subset_univ S)
    have high : mass k S+a < l := by omega
    rw [(well.level' p S).span n a l high,(well.level' p S).coverN a l high]
    exact MarkU.zero.more enough

end YM.Integration.WilsonFiniteDepositedMarkedRows
end

