import YM.Integration.WilsonFiniteMarkedHistoryStep

/-! A genuine marked Wick step needs the quiet and occupied upper incomes only at the
physical fine side of the step. All allowances are still chosen before the cutoff and side. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ} {e m a r : ℕ} {E : Credit}

/-- Positive angular vacuum grades at the single side whose original fine field is read. -/
def PositiveAt (L : Levels G) (O : ChartRatio G) (e N j : ℕ) (n : Side) (s B : ℝ) : Prop :=
  ∀ a, 0 < a → a ≤ e → ∀ l, l+1 ≤ a+2 →
    Sight ((story L O N j).1 n a (l+1)) (actionW L O N j a (l+1)) s B

/-- Every proper and complete occupied face at this side, at the same retained width. -/
def PairedAt (e : ℕ) (Y : Outerm G D) (n : Side) (s A : ℝ) : Prop :=
  ∀ (x : ι → Cover) (S : Finset ι) a, a ≤ e → ∀ l,
    MarkU x S ((Y x S).1 n a l) ((Y x S).2 a l) s (A^S.card)

omit [DecidableEq ι] [Fintype ι] in
theorem narrow {Y : Outerm G D} {n : Side} {t s A B : ℝ} (h : PairedAt e Y n s A)
    (width : t ≤ s) (pay : 0 ≤ A) (bound : A ≤ B) : PairedAt e Y n t B :=
  fun p S a ha l => ((h p S a ha l).mono width).more (pow_le_pow_left₀ pay bound _)

theorem quiet_narrow {L : Levels G} {O : ChartRatio G} {N j : ℕ} {n : Side} {s t A B : ℝ}
    (h : PositiveAt L O e N j n s A) (width : t ≤ s) (pay : A ≤ B) :
    PositiveAt L O e N j n t B :=
  fun a hp he l hl => ((h a hp he l hl).mono width).more pay

theorem prepare (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N (_ : m < N) (n : Side) (V : ℝ), 1 ≤ V →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      ∀ a ≤ e, ∀ l, Sight ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
        (actionW Q.draws Q.paid N (m+1) a l) (holt Q m hm s hs).s (B*V) := by
  obtain ⟨B,hB,free⟩ := WilsonFiniteVacuumFreeInput.original Q hm hs
  refine ⟨B,hB,?_⟩
  intro N cut n V hV issued a ha l
  let q := n*(loose Q.draws m).L
  have more : 0 ≤ B*V := mul_nonneg (zero_le_one.trans hB) (zero_le_one.trans hV)
  cases a with
  | zero => exact (free N cut n l).more (le_mul_of_one_le_right (zero_le_one.trans hB) hV)
  | succ a =>
    let u := (old Q.draws Q.paid Q.hG Q.green N (m+1) cut).basis q
    cases l with
    | zero =>
      have finite := congr_fun (congr_fun u.clear (a+1)) 0
      have cover := congr_fun (congr_fun (catchment Q.draws Q.paid Q.hG Q.green cut).empty (a+1)) 0
      change (0 : Ten ℝ (Site q × Hooks G) 0) = _ at finite
      change (0 : Ten ℝ (Cloth (Hooks G)) 0) = _ at cover
      rw [←finite,←cover]
      exact Sight.zero.more more
    | succ l =>
      by_cases low : l+1 ≤ (a+1)+2
      · apply ((issued (a+1) (Nat.zero_lt_succ _) ha l low).mono ?_).more
          (le_mul_of_one_le_left (zero_le_one.trans hV) hB)
        exact (min_le_left (s/32) _).trans (by linarith)
      · have high : (a+1)+2 < l+1 := by omega
        rw [u.lamp (a+1) (l+1) (by omega),
          post_end (A:=Q.draws) Q.hG Q.green cut (a+1) (l+1) (by omega)]
        exact Sight.zero.more more

theorem face (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (K : ι → ℕ)
    (S : Finset ι) (ha : a ≤ e) (r : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (n:Side) (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      PairedAt e Y (n*(loose Q.draws m).L) s A → ∀ (p : ι → Cover),
      let next := stout Q.draws Q.paid m N K k Y
      MarkU p S ((next p S).1 n a r) ((next p S).2 a r) σ (C*V^d*A^S.card) := by
  obtain ⟨F,hF,quiet⟩ := prepare Q hm hs
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
  intro N cut n Y well V A hV hA prior marked p next
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
    (fun T _ j hj l => (marked x T j hj l).mono small)
  apply row.more
  have bound := mul_le_mul_of_nonneg_left (reset N cut)
    (show 0 ≤ C*(F*V)^d*A^S.card by positivity)
  exact bound.trans_eq (by dsimp [c]; rw [mul_pow]; ring)

/-- Common width on every occupied face, retained order and angular rank.
The marked input price occurs once for each actual source in the output face. -/
theorem posted (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (K : ι → ℕ)
    {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (n:Side) (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      PairedAt e Y (n*(loose Q.draws m).L) s A → PairedAt e (stout Q.draws Q.paid m N K k Y) n σ (C*V^d*A) := by
  classical
  let T := Finset ι × Fin (e+1) × Fin (mass k Finset.univ+e+1)
  choose f c t fees hot row using fun b : T => face (D:=D) (k:=k) Q hm K
    b.1 (Nat.lt_succ_iff.mp b.2.1.isLt) b.2.2.val hs
  obtain ⟨σ,B,d,hσ,hB,room⟩ := WilsonFiniteVacuumWindingReset.common t c f hot fees
  refine ⟨d,B,σ,hB,hσ,?_⟩
  intro N cut n Y well V A hV hA quiet prior x S a ha l
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
    have good := row b N cut n Y well V A hV hA quiet prior x
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

end YM.Integration.WilsonMarkedIndependentPhysicalIntake
end
