import YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticWalls

/-! Spatially separated signed quadratic curl response of the actual original compact one-block course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticChamber
open Function Filter Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet RGComparison.Core16.Forge
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven RGComparison.Core16.Spool RGComparison.Core16.Silk FVA2.CityHistory
open WilsonMatrixTicketLanesReportedWords WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReflectedInner
open WilsonMatrixTicketLanesRetainedAngular WilsonMatrixTicketLanesRetainedCrossed WilsonMatrixTicketLanesRetainedCurls
open WilsonMatrixTicketLanesRetainedQuadraticWalls
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- A single local constant and a positive spatial rate precede every torus, real retained field, tag,
original physical plaquette, and all four color labels. -/
def Bound (b cap : ℕ) (γ C : ℝ) := ∀p : ℕ,
  let S:=R.family.path.levels.clock.op b p
  ∀ (T : Forest S.ratio) (large : Bid.Larger (G:=G) S) (tag : S.Choices)
    (nil : (Descent.nil (top:=R.family.side (b+1) p)).Tags) (u : Directions G (R.family.side b p)),
    (∀e,‖u e‖≤(cap:ℝ)+1) → ∀ (v₀ v₁ v₂ v₃ : Face (Per (R.family.side (b+1) p))) (i j k l : G.ColorIndex)
    (H : ℕ),WilsonMatrixTicketLanesRetainedQuadraticWalls.clear v₀ v₁ v₂ v₃ H →
    |cross (law S T large tag nil) (curl S T v₀ i) (curl S T v₁ j) (curl S T v₂ k) (curl S T v₃ l)
      (changeField S T large tag nil u)| ≤ C / Real.exp (γ*(H:ℝ))

def Before (b cap : ℕ) := ∃γ : ℝ,0<γ ∧ ∃C : ℝ,0≤C ∧ Bound R b cap γ C

theorem fromOffer (b cap : ℕ) {P : Oven (R.family.path.levels.clock.op b 0).patch} (X : P.Form G)
    (offer : P.Offers X R.family.path.levels.clock.kernel) (width : (cap:ℝ)+1≤X.Q)
    {C : ℝ} (nn : 0≤C) (fee : Silk.Past X C 0 2 2) : Bound R b cap (shade X) (256*C) := by
  intro p S T large tag nil u inside a a' c c' i j k l H near
  let Γ:=law S T large tag nil
  let kept:=changeField S T large tag nil u
  let δ:= C / costLamp X H
  have nonneg : 0≤δ:=div_nonneg nn (Real.exp_pos _).le
  have keeping (e) : ‖u e‖≤X.Q:=(inside e).trans width
  let A:=Spool.lens (S:=S) u X T
  have steady : A.Steady:=Oven.paints T offer keeping large
  have price (i₀ i₁ i₂ i₃ : Fin 4) :
      |cross Γ (wire S T (corners a i₀) i) (wire S T (corners a' i₁) j)
        (wire S T (corners c i₂) k) (wire S T (corners c' i₃) l) kept|≤δ := by
    by_cases h₀:corners a i₀∈T.trunks
    · simpa [wire,h₀,cross,PertExtension.GaussianScore.Law.wick] using nonneg
    by_cases h₁:corners a' i₁∈T.trunks
    · simpa [wire,h₁,cross,PertExtension.GaussianScore.Law.wick] using nonneg
    by_cases h₂:corners c i₂∈T.trunks
    · simpa [wire,h₂,cross,PertExtension.GaussianScore.Law.wick] using nonneg
    by_cases h₃:corners c' i₃∈T.trunks
    · simpa [wire,h₃,cross,PertExtension.GaussianScore.Law.wick] using nonneg
    let v₀ : Wire G T.Free:=(⟨corners a i₀,h₀⟩,i)
    let v₁ : Wire G T.Free:=(⟨corners a' i₁,h₁⟩,j)
    let v₂ : Wire G T.Free:=(⟨corners c i₂,h₂⟩,k)
    let v₃ : Wire G T.Free:=(⟨corners c' i₃,h₃⟩,l)
    have far : Silk.Distant A [v₂,v₃] [v₀,v₁] H := by
      intro w hw z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw hz
      rcases hw with rfl|rfl <;> rcases hz with rfl|rfl
      · exact near c (by simp) a (by simp) i₂ i₀
      · exact near c (by simp) a' (by simp) i₂ i₁
      · exact near c' (by simp) a (by simp) i₃ i₀
      · exact near c' (by simp) a' (by simp) i₃ i₁
    have got:=fee _ _ _ _ _ _ _ A steady 0 (le_refl _) [v₂,v₃] (le_refl 2) [v₀,v₁] (le_refl 2) H far
    change |nth 0 (Silk.gap (Spool.lens (S:=S) u X T) [v₂,v₃] [v₀,v₁])|≤δ at got
    rw [WilsonMatrixTicketLanesRetainedCrossed.signed S T large tag nil u X offer keeping v₀ v₁ v₂ v₃] at got
    simpa only [wire,dif_neg h₀,dif_neg h₁,dif_neg h₂,dif_neg h₃] using got
  have result:=plaquettes S T Γ kept a a' c c' i j k l price
  simpa only [δ,Γ,kept,costLamp,mul_div_assoc] using result

theorem original (paid : Paid G R.kit) (cap : ℕ) : ∀ᶠ b : ℕ in atTop,Before R b cap := by
  let empty : Menu G:=code (n:=0) (fun _=>0) (fun i=>i.elim0) 0 cap
  filter_upwards [paid.2 empty] with b sale
  obtain ⟨P,X,U,K,offer,width,rest⟩:=sale
  obtain ⟨C,nn,fee⟩:=Silk.silence offer.good 0 2 2
  exact ⟨shade X,shade_pos,256*C,mul_nonneg (by norm_num) nn,fromOffer R b cap X offer (le_of_eq width.symm) nn fee⟩

end YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticChamber
