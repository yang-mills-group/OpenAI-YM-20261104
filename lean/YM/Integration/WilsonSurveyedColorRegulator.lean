import YM.Integration.WilsonSurveyedColorFlow

/-! Color transport before and after the actual dimensional Mellin integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorRegulator
open Function Set Filter Finset MeasureTheory Real
open MS
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment City
open Momentum Metric Color
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
variable {m n : ℕ} {b : Bool} {K : Rip G} {F H : Mob G} {z : ℂ}

theorem pullsColor (h : m≤n) (F : Rack G n) :
    turn U (pulls h F) = pulls h (turn U F) := by
  funext w
  induction w generalizing F with
  | nil => rfl
  | cons i l ih =>
    rcases i with ⟨⟨a,c⟩,p⟩
    change Koszul.D ((a,c),p) (turn U (pulls h F)) l = _
    rw [derivative]
    change _ = Koszul.D (embA _ (a,c),Left h p) (turn U F) (Arts.lift h l)
    rw [derivative]
    simp only [Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (entry U j c • ·)
      (ih (Koszul.D (((Option.map (rises h) a.1,a.2),j),Left h p) F))

theorem formalTrace (Utable : ∀ i, Arts.Pilot.Transport (pilot U) (K i) (K i))
    (hF : Form0 b F) (hH : Form0 b H) (hK : Knot b K)
    (identified : ∀ n, turn U (F n) = H n) (q : SectorP m) :
    turn U (Wtr z K F q) = Wtr z K H q := by
  have atNat (n : ℕ) (hn : m≤n) : turn U (Wtr n K F q) = Wtr n K H q := by
    have hleft : Wtr n K F q = pulls hn (trc (K n) (Left hn q) (F n)) :=
      funext fun _ => tallyN hF.token hK.token hn
    have hright : Wtr n K H q = pulls hn (trc (K n) (Left hn q) (H n)) :=
      funext fun _ => tallyN hH.token hK.token hn
    have fixe : (pilot (D:=Arts.L n) (P:=SectorP n) U).volp (Left hn q) = Left hn q := rfl
    rw [hleft,hright,pullsColor]
    congr 1
    simpa only [emits,fixe,identified] using (Utable n).shuttle0 (Left hn q) (F n)
  rw [combo z m,map_add,map_smul,map_sub,atNat m (by omega),atNat (m+1) (by omega)]
  exact (combo z m).symm

private theorem integrated {L M : Rack G m → ℂ} (left : L∈Centre _)
    (right : M∈Centre _) (hF : Form0 b F) (hH : Form0 b H) (hK : Knot b K)
    (hz : z∈Town) (same : ∀ p, L (pulls (Nat.le_succ m) (Wtr z K F p)) =
      M (pulls (Nat.le_succ m) (Wtr z K H p))) :
    L (ocean z K F m) = M (ocean z K H m) := by
  obtain ⟨sf,_,hf⟩ := catalog hK hF hz left
  obtain ⟨sh,_,hh⟩ := catalog hK hH hz right
  have slice (x : ℝ) : strand L K F z (x,1) = strand M K H z (x,1) := by
    unfold strand carpet
    rw [← (cent_arguments (Px m) left (f:=fun p l => wing z K F (ray l) ((p,x),1))
      (fun l => (Arc.Q.Gmajor (Px m) (Path.exact_test hF.price hK.price (ray l) z) ()).values (x,1))).2]
    rw [← (cent_arguments (Px m) right (f:=fun p l => wing z K H (ray l) ((p,x),1))
      (fun l => (Arc.Q.Gmajor (Px m) (Path.exact_test hH.price hK.price (ray l) z) ()).values (x,1))).2]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [wing,ray_sail]
    apply same
  have pruned (x : ℝ) := Path.Fiber.pruneC 1 (1:ℝ) (sf.smooth ()) (sh.smooth ()) slice (m+1) x
  rw [← hf,← hh]
  unfold coreC fetching fetchP
  simp only [Pi.smul_apply,pruned]

theorem oceanColor (Utable : ∀ i, Arts.Pilot.Transport (pilot U) (K i) (K i))
    (hF : Form0 b F) (hH : Form0 b H) (hK : Knot b K) (hz : z∈Town)
    (identified : ∀ k, turn U (F k) = H k) :
    turn U (ocean z K F m) = ocean z K H m := by
  funext w
  rw [← emits]
  apply integrated (L:=fun f => (pilot U).beam f w) (M:=fun f => f w)
    ((pilot U).sense.reaches w) (centroid w) hF hH hK hz
  intro p
  rw [emits,pullsColor,formalTrace U Utable hF hH hK identified]

end YM.Integration.WilsonSurveyedColorRegulator
end
