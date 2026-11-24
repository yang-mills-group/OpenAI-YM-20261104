import YM.Integration.WilsonSurveyedColorContinuum

/-! The two enrolled MS books pay all absolute integral prices on their own
earlier rows. Uniqueness at each cardinality and degree first identifies
those earlier rows, so the price of a separately rotated packet is unnecessary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorBank
open Function Set Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone City Latch Latch.Job Rake Arts Osc Snap
open Land Local.Physical Rake.Geo Tide Vane
open WilsonSurveyedColorQuotient WilsonSurveyedColorFlow WilsonSurveyedColorHearing
open WilsonSurveyedColorContinuum
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
variable {I W : Type} [LinearOrder W]
local notation "Z" => constantP G I (PlanetD G)
local notation "μ" => (fun _ : I => planeF)

private theorem earned {K : Planet G I} {F H : Glade G I} (hF : Warm F false)
    (hH : Warm H false) (hK : BackF K) (i : I) (t : ℝ) (A : QP) :
    SatP planeF (K i t) (F i t) (H i t) A := by
  let T := ‖t‖+1
  have ht : 0≤T := by dsimp [T]; positivity
  let p : camp T := ⟨(),t,existsC t⟩
  obtain ⟨_,_,hv⟩ := Job.funds (camp T) Coherent
  exact priceP (hK.cost i T ht) (hF.cost i T ht).highp (hH.cost i T ht).highp hv p A

theorem together {x : Position W I} {P P' : Geo I} {B B' : Site G I}
    {V V' : W → Site G I} {sizes sizes' : W → ℕ} {X Y : Dance G I W}
    (ua : Tour Z Z P x false B V sizes) (ub : Tour Z Z P' x false B' V' sizes')
    (left : Fields x μ Z Z B V X) (right : Fields x μ Z Z B' V' Y)
    (vacuum : ∀ k, filed U (B k) = B' k)
    (names : ∀ a k, filed U (V a k) = V' a k) :
    ∀ s k, filed U (X s k) = Y s k := by
  intro s
  induction s using Finset.strongInductionOn
  rename_i s older
  by_cases count : 2≤s.card
  · intro n
    induction n using Nat.strong_induction_on with
    | h k lower =>
      have ne : s.Nonempty := Finset.card_pos.mp (by omega)
      have fee := Rake.Sat_W (founded ua left ne k).2 ua.ground.pool (fun _ => Coherent)
      have pay := step U (left.2.2 s count k) (propagates U μ _ fee)
      have rhs := right.2.2 s count k
      have equal : filed U (multi μ x Z Z B (X s) X k s) = multi μ x Z Z B' (Y s) Y k s := by
        unfold multi lonely
        simp only [map_add,map_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hJ := lower j (Finset.mem_Ico.mp hj).2
          funext i t
          have c := connected U (Landau.line (Real.exp t)) (B (k-j) i t) (X s j i t)
            (freeLine t)
          exact c.trans (congrArg₂ (Flux.tree Landau.parity (PlanetD G t))
            (congrFun (congrFun (vacuum (k-j)) i) t) (congrFun (congrFun hJ i) t))
        · refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun j _ => ?_
          have small := n_small hz
          have eF := older z small.1 j.1
          have eH := older (s\z) small.2.2.2 j.2
          funext i t
          let A := (rootX x z - rootX x s) i
          have lpay := earned (founded ua left small.2.1 j.1).2
            (founded ua left small.2.2.1 j.2).2 ua.ground.pool i t A
          have rpay := earned (founded ub right small.2.1 j.1).2
            (founded ub right small.2.2.1 j.2).2 ub.ground.pool i t A
          have hf : turn U (X z j.1 i t) = Y z j.1 i t := congrFun (congrFun eF i) t
          have hh : turn U (X (s\z) j.2 i t) = Y (s\z) j.2 i t := congrFun (congrFun eH i) t
          rw [← hf,← hh] at rpay
          have c := WilsonSurveyedColorContact.contact U A (Landau.line (Real.exp t))
            _ _ _ lpay rpay
          rw [hf,hh] at c
          exact c
      rw [equal] at pay
      exact Duty.consistent (retire Z μ) pay rhs
  · rcases (by omega : s.card=0 ∨ s.card=1) with zero | one
    · rw [Finset.card_eq_zero.mp zero]
      intro k
      simp [left.1,right.1]
    · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp one
      intro k
      rw [left.2.1 a,right.2.1 a]
      exact names a k

variable {B B' : Deck G} {O : Booked B} {O' : Booked B'}
theorem labelled {A : MS_Data G O} {A' : MS_Data G O'} {u : W → Rake.Label B}
    {u' : W → Rake.Label B'} {x : W → QP} (hp : Injective x) (ν : ℝ)
    (vacuum : ∀ k, filed U (approach (frameF Unit ν) A k) = approach (frameF Unit ν) A' k)
    (names : ∀ w k, filed U (rowM (frameF Unit ν) A (u w) k) =
      rowM (frameF Unit ν) A' (u' w) k) :
    Dial.tour A u ν x = Dial.tour A' u' ν x := by
  have H : Mesh (frameF Unit ν) (fun w (_ : Unit) => x w) := by
    intro i j hi
    have he : 0<‖x i-x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hp.ne hi))
    exact ⟨⟨_,he,fun _ => by simp [roots]⟩,⟨_,he,fun _ => by simp [roots]⟩⟩
  apply ordinary U _ ()
  funext s k
  exact together U (builder A H u) (builder A' H u') (Dial.pin A u ν hp)
    (Dial.pin A' u' ν hp) vacuum names s k

end YM.Integration.WilsonSurveyedColorBank
end
