import YM.Integration.WilsonDepositedRegisteredWinding
import YM.Integration.OriginalCoverReanchoring

/-! A common incoming winding allowance for the first deposited marked bank
on the original Wilson run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCommonDepositedWinding
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D k : ι → ℕ} {I : ι → Type} [∀ i, Fintype (I i)]

/-- The complete deposited family fits one width and one allowance before
all periods, placements and ordered tests. Empty and out-of-shell tensors
are exactly zero on both sides of the comparison. -/
theorem retained {e m : ℕ} (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (X : ∀ i, I i → Seed G (D i)) (w : Gear G → ℝ) (hw : ∀ B, 0 < w B)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (K : ι → ℕ) :
    let Y := Gears Q.draws Q.paid K k (m+1) (m+1) m (independent X)
    ∃ σ A : ℝ, 0 < σ ∧ 1 ≤ A ∧ ∀ (n : Side) (p : ι → Cover)
      (S : Finset ι) (a : ℕ), a ≤ e → ∀ r, MarkU p S ((Y p S).1 n a r) ((Y p S).2 a r)
        σ (A^S.card) := by
  classical
  intro Y
  let T := Finset ι × Fin (e+1) × Fin (mass k Finset.univ+e+1)
  have pair (t : T) := WilsonDepositedRegisteredWinding.first (r:=t.2.2.val) Q hm X w hw hX K
    Finset.univ t.1 (subset_univ _) (Nat.lt_succ_iff.mp t.2.1.isLt)
  choose σ B hσ hB row using pair
  have hn : (Finset.univ : Finset T).Nonempty := ⟨(∅,0,0),mem_univ _⟩
  let s := Finset.univ.inf' hn σ
  let A := max 1 (Finset.univ.sup' hn B)
  have hs : 0 < s := by
    simpa only [s,Finset.lt_inf'_iff] using (show ∀ t ∈ Finset.univ, 0 < σ t from fun t _ => hσ t)
  have ha : 1 ≤ A := le_max_left ..
  have well := (OriginalCoverReanchoring.iterated (k:=k) X Q.draws Q.paid K
    (j:=m) (b:=m+1) (N:=m+1) (Nat.le_succ m) le_rfl Q.hG Q.green hX).1
  refine ⟨s,A,hs,ha,?_⟩
  intro n p S a he r
  have hfee : 0 ≤ A^S.card := pow_nonneg (zero_le_one.trans ha) _
  by_cases h0 : S = ∅
  · subst S
    have quiet : Y p ∅ = 0 := well.quiet' p
    rw [quiet]
    exact MarkU.zero.more hfee
  by_cases hr : r < mass k Finset.univ + e + 1
  · let t : T := (S,⟨a,Nat.lt_succ_iff.mpr he⟩,⟨r,hr⟩)
    have money : B t ≤ A := (Finset.le_sup' B (mem_univ t)).trans (le_max_right ..)
    have nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    exact ((row t n p).mono (Finset.inf'_le σ (mem_univ t))).more
      (money.trans (le_self_pow₀ ha (Nat.ne_of_gt (Finset.card_pos.mpr nonempty))))
  · have hmS : mass k S ≤ mass k Finset.univ := by
      unfold mass
      exact Finset.sum_le_sum_of_subset (subset_univ S)
    have high : mass k S + a < r := by omega
    have law := well.level' p S
    have finite : (Y p S).1 n a r = 0 := law.span n a r high
    have cover : (Y p S).2 a r = 0 := law.coverN a r high
    rw [finite,cover]
    exact MarkU.zero.more hfee

end YM.Integration.WilsonCommonDepositedWinding
end
