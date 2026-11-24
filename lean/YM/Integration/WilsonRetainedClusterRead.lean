import YM.Integration.WilsonRetainedMoleculeRead
import YM.Integration.WilsonRetainedBareFactor
import YM.Integration.ManuscriptQLocalIntegratedTicket

/-! The linked coefficient of the submitted original Laurent mask as
  a product of its actual conditional Haar and Gaussian integrals. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRetainedClusterRead
open Function Finset Lattice Wilson Merge RG Tree Pressure ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat Lotus Daisy RGLocalTaylor MergeProof Marker Extra.Multi
open Matter
open ManuscriptQLocalMarkedHeightTail ManuscriptQLocalIntegratedTicket WilsonRetainedMoleculeRead
open scoped Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ α : ℝ} {o : Target.Order G W}
    (H : Cash W s μ L Q o α T R) (χ : Chi)
    {V ι : Type} [DecidableEq V] [Fintype ι] {Γ : Marker.Census V} (M : ι→Menu.Hat Γ R)
    {j n : ℕ} {C' d v Y A b r B q : ℝ} (N : Captain H j C' d v Y A b r B q n χ)
local notation "rows" => (fun i : ι => (M i).M)

def integral (p : Ursell.Clusters H.ThinP) (D : Captain.Oscars rows p) (U : Config G c) : ℝ :=
  Ursell.coefficient H.seam p.2*(∏b,localRead H χ rows (p.2 b) (D b) U) / ↑(p.1+1).factorial

include N
omit [Fintype ι] in
theorem activity_eq (p : Ursell.Clusters H.ThinP) (D : Captain.Oscars rows p) (U : Config G c) :
    activity H χ M p D U=integral H χ M p D U := by
  unfold activity integral
  simp_rw [factor H χ rows N]

theorem occupied (w : V→ℝ) (hw : ∀v,0<w v) (p : H.fragrances) (U : Config G c)
    (z : Γ.Mode) (marked : z≠Γ.quiet) :
    (Merge.Photo.headSheet rows H χ (fun i=>Menu.sumFee (M i) w) Γ
      (fun i=>Menu.sing (M i) w) p U).part z =
      ∑D:Captain.Oscars rows p,(integral H χ M p D U:ℂ)*(matrix H M ⟨p,D⟩).part z := by
  rw [ManuscriptQLocalIntegratedTicket.marked H χ M w hw p U z marked]
  simp_rw [activity_eq H χ M N]

/-- The physical logarithm at one linked cluster. Every signed component is
  heard on its own original mask, with the same compact coarse input. -/
def bare (p : H.fragrances) (D : Captain.Oscars rows p) (U : Config G c) : ℝ :=
  if ∀b, authorized H (p.2 b).val then
    Ursell.coefficient H.seam p.2 * (∏b, RG.masked (Pressure.temp s) (H.unionP (p.2 b).val)
      (WilsonRetainedBareFactor.sampled H χ rows (p.2 b) (D b)) U) / ↑(p.1+1).factorial
  else 0

omit [Fintype ι] in
theorem low_activity (ℓ : ℕ) (p : H.fragrances) (low : ¬Height.tiredN H ℓ p)
    (D : Captain.Oscars rows p) (U : Config G c) :
    activity H χ M p D U=bare H χ M p D U := by
  by_cases eligible : ∀b, authorized H (p.2 b).val
  · have young := (Height.aged (H:=H) eligible low).1
    unfold activity bare
    rw [if_pos eligible]
    congr 2
    exact Finset.prod_congr rfl fun b _=>
      WilsonRetainedBareFactor.factor H χ rows _ _ U (young b).unforced (eligible b)
  unfold activity bare
  rw [if_neg eligible]
  obtain ⟨b,absent⟩ := Classical.not_forall.mp eligible
  have zero : Palette.act rows H χ U (p.2 b).val (D b) = 0 := by
    rw [factor H χ rows N,localRead,if_neg fun h=>absent h.1]
  rw [Finset.prod_eq_zero (Finset.mem_univ b) zero,mul_zero,zero_div]

theorem low_occupied (ℓ : ℕ) (p : H.fragrances) (low : ¬Height.tiredN H ℓ p)
    (w : V→ℝ) (hw : ∀v,0<w v) (U : Config G c) (z : Γ.Mode) (marked : z≠Γ.quiet) :
    (Merge.Photo.headSheet rows H χ (fun i=>Menu.sumFee (M i) w) Γ
      (fun i=>Menu.sing (M i) w) p U).part z =
      ∑D:Captain.Oscars rows p,(bare H χ M p D U:ℂ)*(matrix H M ⟨p,D⟩).part z := by
  rw [ManuscriptQLocalIntegratedTicket.marked H χ M w hw p U z marked]
  simp_rw [low_activity H χ M N ℓ p low]

end YM.Integration.WilsonRetainedClusterRead
