import YM.Integration.WilsonFiniteDepositedMarkedRows

/-! Paired finite and cover marked rows through an actual nonbare update,
including the integration over every original back address. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteMarkedHistoryStep
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D k : ι → ℕ} {e m a r : ℕ}

/-- The same paired tensor, including rank zero, at each marked root and finite side. -/
def paired (e : ℕ) (Y : Outerm G D) (s A : ℝ) : Prop :=
  ∀ (n : Side) (x : ι → Cover) (S : Finset ι) a, a ≤ e → ∀ l,
    MarkU x S ((Y x S).1 n a l) ((Y x S).2 a l) s (A^S.card)

theorem face (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (K : ι → ℕ)
    (S : Finset ι) (ha : a ≤ e) (r : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) s V →
      paired e Y s A → ∀ (n : Side) (p : ι → Cover),
      let next := stout Q.draws Q.paid m N K k Y
      MarkU p S ((next p S).1 n a r) ((next p S).2 a r) σ (C*V^d*A^S.card) := by
  obtain ⟨F,hF,quiet⟩ := WilsonFiniteVacuumWindingDate.prepare Q hm hs
  obtain ⟨W,hW,reset⟩ := WilsonFiniteVacuumWindingReset.rim Q hm ha r
  obtain ⟨d,C,σ,hC,hσ,step⟩ := WilsonFiniteIncomingMarkedWinding.original
    (D:=D) (k:=k) (r:=r) Q hm (subset_univ S) ha hs
  let P := loose Q.draws m
  let c := C*F^d*W
  let b := scalesK P K S * ∑ _ : backRow P.L S, c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb : 0 ≤ b := mul_nonneg (scalesBound P K S) (Finset.sum_nonneg fun _ _ => hc)
  have small : (holt Q m hm s hs).s ≤ s := by
    have hh : (holt Q m hm s hs).s ≤ s/32 := min_le_left ..
    linarith
  refine ⟨d,b,σ,hb,hσ,?_⟩
  intro N cut Y well V A hV hA prior marked n p next
  have fee : scalesK P K S * ∑ _ : backRow P.L S, c*V^d*A^S.card = b*V^d*A^S.card := by
    rw [←Finset.sum_mul,←Finset.sum_mul]
    dsimp only [b]
    ring
  rw [←fee]
  apply WilsonDepositedRegisteredWinding.addressed P K (fun x => logO Q.draws Q.paid m N (Y x) k)
    p S n a r σ (fun _ => c*V^d*A^S.card)
  intro j
  let cell := inflate P S j
  let x := chartIn P p cell
  have row := step N cut n (Y x) p cell (well.quiet' x) (well.level' x) (F*V) A
    (one_le_mul_of_one_le_of_one_le hF hV) (zero_le_one.trans hA) (quiet N cut n V hV prior)
    (fun T _ j hj l => (marked (n*P.L) x T j hj l).mono small)
  apply row.more
  have bound := mul_le_mul_of_nonneg_left (reset N cut)
    (show 0 ≤ C*(F*V)^d*A^S.card by positivity)
  exact bound.trans_eq (by dsimp [c]; rw [mul_pow]; ring)

/-- Common width on every occupied face, retained order and angular rank.
The marked input price occurs once for each actual source in the output face. -/
theorem original (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (K : ι → ℕ)
    {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) s V →
      paired e Y s A → paired e (stout Q.draws Q.paid m N K k Y) σ (C*V^d*A) := by
  classical
  let T := Finset ι × Fin (e+1) × Fin (mass k Finset.univ+e+1)
  choose f c t fees hot row using fun b : T => face (D:=D) (k:=k) Q hm K
    b.1 (Nat.lt_succ_iff.mp b.2.1.isLt) b.2.2.val hs
  obtain ⟨σ,B,d,hσ,hB,room⟩ := WilsonFiniteVacuumWindingReset.common t c f hot fees
  refine ⟨d,B,σ,hB,hσ,?_⟩
  intro N cut Y well V A hV hA quiet prior n x S a ha l
  let W := stout Q.draws Q.paid m N K k Y
  have sound := Seating Q.draws Q.paid Y Q.hG Q.green cut well K
  have one : 1 ≤ B*V^d := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hV)
  have enough := pow_nonneg (zero_le_one.trans (one_le_mul_of_one_le_of_one_le one hA)) S.card
  by_cases empty : S = ∅
  · subst S
    rw [sound.quiet' x]
    exact MarkU.zero.more (by positivity)
  by_cases within : l < mass k Finset.univ+e+1
  · let b : T := (S,⟨a,Nat.lt_succ_iff.mpr ha⟩,⟨l,within⟩)
    have good := row b N cut Y well V A hV hA quiet prior n x
    have card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    apply (good.mono (room b).1).more
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (((room b).2 V hV).trans
      (le_self_pow₀ one (Nat.ne_of_gt card))) (pow_nonneg (zero_le_one.trans hA) _)
  · have hmS : mass k S ≤ mass k Finset.univ := by
      unfold mass; exact Finset.sum_le_sum_of_subset (subset_univ S)
    have high : mass k S+a < l := by omega
    rw [(sound.level' x S).span n a l high,(sound.level' x S).coverN a l high]
    exact MarkU.zero.more enough

end YM.Integration.WilsonFiniteMarkedHistoryStep
