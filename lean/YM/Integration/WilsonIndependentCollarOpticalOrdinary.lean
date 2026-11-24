import YM.Integration.WilsonIndependentCollarOrdinaryAlgebra
import YM.Integration.WilsonIndependentCollarOpticalWidth

/-! The actual deposited child bank at the original positive teacher
width on an arbitrarily long optical interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalOrdinary
open Function Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonReceivedFixedDigitHistory WilsonIndependentCollarOrdinaryAlgebra
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

private lemma seats {C F A:ℝ} (fee:C≤F) (cost:1≤F) (hA:0≤A) {n:ℕ} (live:0<n):
    C*A^n≤(F*A)^n:=by
  rw [mul_pow];exact mul_le_mul_of_nonneg_right (fee.trans (le_self_pow₀ cost live.ne')) (pow_nonneg hA _)

theorem weak (Q:Realm G (e+1) Credit.leanC) (N:ℕ) (cell:Digits Q.draws ι) (Y:Outerm G D)
    (well:Wellness k Y) (m days:ℕ) (hm:Q.anchor ≤ m) (cut:m+days≤N)
    (A C F Z:ℝ) (hA:0≤A) (hC:1≤C) (hF:1≤F) (room:PadRank Q m (m+days) Z)
    (algebra:∀S:Finset ι,cost e (mass k univ+e) S≤C)
    (bulk:∀S:Finset ι,(WilsonIndependentCollarOrdinaryWeak.price G (mass k S) e).buy Z≤F)
    (dorm:∀S:Finset ι,Dormitory Q (mass k S) 0 Credit.leanC)
    (seed:∀ y S, S.Nonempty → ∀ f:Pen D S →L[ℝ] ℝ,‖f‖≤1 →
      Saturation e 0 0 (tuftV f (levelsO (Y y) S)).2 0 (A^S.card))
    (y:ι → Cover) (S:Finset ι):
    shingled y S (itinerary Q.draws Q.paid k N cell days m Y) e 0 (C*(F*A)):=by
  let Z':=itinerary Q.draws Q.paid k N cell days m Y
  have hw:Wellness k Z':=sound Q.draws Q.paid k N cell Q.hG Q.green Y well days m cut
  intro q hq r
  refine ⟨by positivity,?_⟩
  intro x; simp only [neg_zero,zero_mul,Real.exp_zero,mul_one]
  by_cases hs:S.Nonempty
  · by_cases rank:r ≤ mass k univ+e
    · have priced (J:Finset ι) (hJ:J.Nonempty):Capped e (mass k univ+e) (levelsO (Z' y) J).2 ((F*A)^J.card):=by
        intro i hi r _ x
        have uncut:=WilsonIndependentCollarOrdinaryWeak.original Q N cell Y well J days m y hm cut
          Z (A^J.card) room (pow_nonneg hA _) (dorm J) (seed _ J hJ) i r hi
        have fee:=seats (bulk J) hF hA (Finset.card_pos.mpr hJ)
        simpa using (uncut.more fee).2 x
      have fit:=WilsonIndependentCollarOrdinaryAlgebra.original (levelsO (Z' y)) (F*A)
        (mul_nonneg (zero_le_one.trans hF) hA) priced S q hq r rank x
      rw [rectify (Z' y) (hw.level' y) (hw.quiet' y)] at fit
      exact fit.trans (seats (algebra S) hC (mul_nonneg (zero_le_one.trans hF) hA) (Finset.card_pos.mpr hs))
    · have smallest:mass k S ≤ mass k univ:=by rw [stairK k (Finset.subset_univ S)];exact Nat.le_add_right ..
      have hz:((Z' y S).2 q r)=0:=(hw.level' y S).coverN q r (by omega)
      change ‖(Z' y S).2 q r x‖≤_;rw [hz];simp only [Pi.zero_apply,norm_zero];positivity
  · have empty:S=∅:=Finset.not_nonempty_iff_eq_empty.mp hs;subst S
    change ‖(Z' y ∅).2 q r x‖≤_;rw [hw.quiet' y];change ‖(0:Pen D ∅)‖≤_;simp

/-- Single-power source dossier throughout a growing optical interval.
The price and all printed widths are those of the same dated original course. -/
theorem original (Q:Realm G (e+1) Credit.leanC) (policy:Cloze D k Q Credit.leanC)
    (N:ℕ) (cell:Digits Q.draws ι) (Y:Outerm G D) (well:Wellness k Y)
    (m days:ℕ) (hm:Q.anchor ≤ m) (cut:m+days≤N) (A C F T Z:ℝ)
    (hA:0≤A) (hC:1≤C) (hF:1≤F) (hT:1≤T) (room:PadRank Q m (m+days) Z)
    (algebra:∀S:Finset ι,cost e (mass k univ+e) S≤C)
    (bulk:∀S:Finset ι,(WilsonIndependentCollarOrdinaryWeak.price G (mass k S) e).buy Z≤F)
    (dorm:∀S:Finset ι,Dormitory Q (mass k S) 0 Credit.leanC)
    (seed:∀ y S, S.Nonempty → ∀ f:Pen D S →L[ℝ] ℝ,‖f‖≤1 →
      Saturation e 0 0 (tuftV f (levelsO (Y y) S)).2 0 (A^S.card))
    (price:∀ j, m ≤ j → j < m+days → Q.cash (vigor G D k e Credit.leanC Credit.leanC) j ≤ T)
    (width:∀ j (hj:Q.anchor≤ j), m ≤ j → j < m+days →
      2*elixir (Q.mint j hj).gear=3*(Q.mint j hj).σ)
    (incoming:Uniform Q Y (m+days) (by omega) (T^2*(C*(F*A)))):
    Uniform Q (itinerary Q.draws Q.paid k N cell days m Y) m hm (T^2*(C*(F*A))):=by
  apply WilsonIndependentCollarOpticalWidth.original Q policy N cell Y well _ T (by positivity)
    hT days m hm cut price width _ incoming
  intro j d jm top y S
  apply weak Q N cell Y well j d (by omega) (by omega) A C F Z hA hC hF _ algebra bulk dorm seed y S
  exact ⟨fun p h t=>room.year p (by omega) (by omega),by
    rw [top];exact (Nat.cast_le.mpr (show m+days-j ≤ m+days-m by omega)).trans room.lengthS⟩

end YM.Integration.WilsonIndependentCollarOpticalOrdinary
end
