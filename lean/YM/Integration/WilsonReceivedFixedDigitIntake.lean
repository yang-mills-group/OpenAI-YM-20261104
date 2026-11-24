import YM.Integration.WilsonMarkedIndependentPhysicalIntake

/-! The genuine unaveraged connected marked step on one separately fixed fine residue at each name. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFixedDigitIntake
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ} {e m a r : ℕ} {E : Credit}

open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt prepare)

def next (L:Levels G)(O:ChartRatio G)(m N:ℕ)(k:ι→ℕ)(Y:Outerm G D)
    (digit:ι→Site (loose L m).L):Outerm G D:=
  fun y=>logO L O m N (Y (chartIn (loose L m) y digit)) k

omit [Fintype ι] in
theorem lawful (L:Levels G)(O:ChartRatio G)(m N:ℕ)(k:ι→ℕ)(Y:Outerm G D)
    (digit:ι→Site (loose L m).L)(simple:G.Simple)(ratio:LocalRatio O)(live:m<N)(well:Wellness k Y):
    Wellness k (next L O m N k Y digit):=by
  refine ⟨fun y=>logHush L O m N _ k,fun y=>step_L L O m N _ k live simple ratio (well.level' _),?_⟩
  intro y z S same
  apply log_g
  intro T sub
  apply well.filial
  intro a used
  simp only [chartIn,same a (sub used)]

theorem face (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) 
    (S : Finset ι) (ha : a ≤ e) (r : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (n:Side) (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      PairedAt e Y (n*(loose Q.draws m).L) s A → ∀ (cell:ι→Site (loose Q.draws m).L) (p : ι → Cover),
      let output := next Q.draws Q.paid m N k Y cell
      MarkU p S ((output p S).1 n a r) ((output p S).2 a r) σ (C*V^d*A^S.card) := by
  obtain ⟨F,hF,quiet⟩ := prepare Q hm hs
  obtain ⟨W,hW,reset⟩ := WilsonFiniteVacuumWindingReset.rim Q hm ha r
  obtain ⟨d,C,σ,hC,hσ,step⟩ := WilsonFiniteIncomingMarkedWinding.original
    (D:=D) (k:=k) (r:=r) Q hm (subset_univ S) ha hs
  let P := loose Q.draws m
  let c := C*F^d*W
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have small : (holt Q m hm s hs).s ≤ s := by
    have hh : (holt Q m hm s hs).s ≤ s/32 := min_le_left ..
    linarith
  refine ⟨d,c,σ,hc,hσ,?_⟩
  intro N cut n Y well V A hV hA prior marked cell p output
  let x := chartIn P p cell
  have row := step N cut n (Y x) p cell (well.quiet' x) (well.level' x) (F*V) A
    (one_le_mul_of_one_le_of_one_le hF hV) (zero_le_one.trans hA) (quiet N cut n V hV prior)
    (fun T _ j hj l => (marked x T j hj l).mono small)
  apply row.more
  have bound := mul_le_mul_of_nonneg_left (reset N cut)
    (show 0 ≤ C*(F*V)^d*A^S.card by positivity)
  exact bound.trans_eq (by dsimp [c]; rw [mul_pow]; ring)

theorem posted (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) 
    {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ (n:Side) (Y : Outerm G D),
      Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      PairedAt e Y (n*(loose Q.draws m).L) s A → ∀cell:ι→Site (loose Q.draws m).L, PairedAt e (next Q.draws Q.paid m N k Y cell) n σ (C*V^d*A) := by
  classical
  let T := Finset ι × Fin (e+1) × Fin (mass k Finset.univ+e+1)
  choose f c t fees hot row using fun b : T => face (D:=D) (k:=k) Q hm
    b.1 (Nat.lt_succ_iff.mp b.2.1.isLt) b.2.2.val hs
  obtain ⟨σ,B,d,hσ,hB,room⟩ := WilsonFiniteVacuumWindingReset.common t c f hot fees
  refine ⟨d,B,σ,hB,hσ,?_⟩
  intro N cut n Y well V A hV hA quiet prior cell x S a ha l
  let W := next Q.draws Q.paid m N k Y cell
  have sound := lawful Q.draws Q.paid m N k Y cell Q.hG Q.green cut well
  have one : 1 ≤ B*V^d := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hV)
  have enough := pow_nonneg (zero_le_one.trans (one_le_mul_of_one_le_of_one_le one hA)) S.card
  by_cases empty : S = ∅
  · subst S
    rw [sound.quiet' x]
    exact MarkU.zero.more (by positivity)
  by_cases within : l < mass k Finset.univ+e+1
  · let b : T := (S,⟨a,Nat.lt_succ_iff.mpr ha⟩,⟨l,within⟩)
    have good := row b N cut n Y well V A hV hA quiet prior cell x
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

end YM.Integration.WilsonReceivedFixedDigitIntake
end
