import YM.Integration.PhysicalAffineScalarComparison
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore

/-! Restore every signed row of the manuscript's affine square, including a
row whose determining stencil missed the old active tree. The latter row is
constant in the free variables. Its possibly field- and tree-dependent value
moves from the interaction into the Gaussian scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarAperture

open Function Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open PhysicalAffineScalarComparison
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {σ E Λ : ℝ}
  (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
  (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ)
  (Y : LinkArray G (Frozen A x F))
local notation "W" => shots S x
local notation "keys" => Rows.In (G:=G) x A F
local notation "mat" => Rows.gram T x V k W A F

/-- Material value on the physical signed row, prior to the aperture selection. -/
def materialRow (m : Prices G (Active A x F)) (i : Slots S) : G.Color :=
  slip • Rows.lands T x V k W A F q d Y m i

/-- Value attained when every active derivative on the row vanishes. -/
def constantRow (i : Slots S) : G.Color :=
  slip • (Rows.base T x V k i + Rows.bump T x V k (Rows.input x A F (autoShell q d V Y)) i)

theorem restore (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds p σ E Λ)
    (m : Prices G (Active A x F)) (i : Slots S) :
    materialRow T x V k A F q d Y m i =
    if Rows.keep x W A F i then tape (Rows.direct T x V k W A F q d Y m) i
    else constantRow T x V k A F q d Y i := by
  obtain ⟨s,i⟩ := i
  by_cases hi : Rows.keep x W A F (s,i)
  · rw [if_pos hi]
    have hr := congr_fun (Rows.arrived T x V k W A F q d Y hT m) (s,i)
    simpa only [Rows.restrict,if_pos hi,materialRow] using hr.symm
  · rw [if_neg hi]
    have hs := skip_bump T x V k A F s i (tape m) h hi
    simp only [materialRow,constantRow,Rows.lands,Rows.bump_add T x V k hT,Pi.add_apply,hs,add_zero]

def omittedAt (s : Site c) : ℝ := ∑ i : Rows.Receipt G S,
  if rowRoot S i = s ∧ ¬Rows.keep x W A F i.1 then (constantRow T x V k A F q d Y i.1 i.2)^2/2 else 0

def allAt (s : Site c) (m : Prices G (Active A x F)) : ℝ := ∑ i : Rows.Receipt G S,
  if rowRoot S i=s then (materialRow T x V k A F q d Y m i.1 i.2)^2/2 else 0

def selectedAt (s : Site c) (m : Prices G (Active A x F)) : ℝ := ∑ i : Rows.Receipt G S,
  if rowRoot S i=s then (Rows.direct T x V k W A F q d Y m i)^2/2 else 0

/-- The missed offset is present at precisely the same translation root. -/
theorem restored_square (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds p σ E Λ)
    (s : Site c) (m : Prices G (Active A x F)) :
    allAt T x V k A F q d Y s m =
      selectedAt T x V k A F q d Y s m + omittedAt T x V k A F q d Y s := by
  unfold allAt selectedAt omittedAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with ⟨i,l⟩
  by_cases hs : rowRoot S (i,l)=s
  · by_cases hi : Rows.keep x W A F i
    · simp only [hs,hi,not_true_eq_false,and_false,if_true,if_false,add_zero,
        restore T x V k A F q d Y h hT m,tape_ap]
    · have zero : Rows.direct T x V k W A F q d Y m (i,l)=0 := by
        change tape (Rows.direct T x V k W A F q d Y m) i l=0
        rw [Rows.arrived T x V k W A F q d Y hT,Rows.restrict,if_neg hi]
        rfl
      simp [hs,hi,zero,restore T x V k A F q d Y h hT m]
  · simp [hs]

theorem sum_selected (m : Prices G (Active A x F)) :
    ∑ s : Site c, selectedAt T x V k A F q d Y s m = Rows.guide T x V k W A F q d Y m := by
  unfold selectedAt Rows.guide dotProduct
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,← Finset.sum_div,sq]

/-- The original nonlinear fee on the actual material field, with its
interaction and affine scalar recomputed simultaneously. -/
theorem interaction (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds p σ E Λ)
    (U : Config G f) (m : Prices G (Active A x F)) :
    Rows.fee T x V k A U =
      (averaged (Rows.residual T x V k W A F q d Y U m) -
        ∑ s : Site c, omittedAt T x V k A F q d Y s) +
        ∑ s : Site c, allAt T x V k A F q d Y s m := by
  simp_rw [restored_square T x V k A F q d Y h hT,Finset.sum_add_distrib,
    sum_selected T x V k A F q d Y]
  rw [Rows.exact_fee,Rows.compose_residual T x V k W A F q d Y hT]
  ring

/-- The full constant-row restoration at the physical stationary center.
A nonempty tag dependence of the omitted portion is allowed. -/
theorem stationary (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds p σ E Λ)
    (H₀ : Gaussian.Table keys) (h₀ : H₀.PosDef) (hQ : (mat).PosDef)
    (g : ℝ) (hg : 0<g) (z : Prices G (Active A x F)) :
    let m := PhysicalAffineScalarComparison.stationary T x V k W A F q d Y
    Real.log (chartCost mat⁻¹ g / chartCost H₀⁻¹ g) +
      Rows.adjustment T x V k W A F q d Y mat⁻¹ m g z -
      (∑ s : Site c, omittedAt T x V k A F q d Y s)/g^2 =
        (Real.log H₀.det-Real.log (mat).det)/2 -
        (∑ s : Site c, allAt T x V k A F q d Y s m)/g^2 := by
  intro m
  have hh := stationary_scalar T x V k W A F q d Y H₀ h₀ hQ hg z
  change _ + Rows.adjustment _ _ _ _ _ _ _ _ _ _ _ m _ _ = _ at hh
  rw [hh,← rooted_square T x V k W A F q d Y]
  simp_rw [restored_square T x V k A F q d Y h hT,Finset.sum_add_distrib,
    sum_selected T x V k A F q d Y]
  ring

def noHole (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩

theorem no_frozen (F : Forest S.ratio) (y : LogArray G (Frozen (noHole S) x F)) :
    Rows.input x (noHole S) F y=0 := by
  funext i
  unfold Rows.input
  split
  next hn =>
    have hc : ¬chill (noHole S) x F ⟨i,hn⟩ := (Native.every F x ⟨i,hn⟩).property
    rw [dif_neg hc]; rfl
  · rfl

/-- The reference half-log of the actual no-hole chart is common to the
old and changed tree as well as to the predictor choices. -/
theorem flat_det (F' : Forest S.ratio) (k' : S.Choices) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds p σ E Λ) :
    (Rows.gram T x 1 k W (noHole S) F).det = (Rows.gram T x 1 k' W (noHole S) F').det := by
  have hc (U : Forest S.ratio) (u : S.Choices) :
      (Rows.gram T x 1 u W (noHole S) U).det = (Native.kinetic T U u x).det := by
    let e : U.Free × G.ColorIndex ≃ Active (noHole S) x U × G.ColorIndex := Native.lineEquiv U x
    have he : (Rows.gram T x 1 u W (noHole S) U).submatrix e e = Native.kinetic T U u x := by
      exact Native.ground_gram T U u x h
    simpa only [Matrix.det_submatrix_equiv_self] using congrArg Matrix.det he
  rw [hc,hc]
  exact Native.shared T F F' k x hT h k'

theorem flat_chart (F' : Forest S.ratio) (k' : S.Choices) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds p σ E Λ) (g : ℝ) :
    chartCost (Rows.gram T x 1 k W (noHole S) F)⁻¹ g =
    chartCost (Rows.gram T x 1 k' W (noHole S) F')⁻¹ g := by
  have he := ((Native.lineEquiv (G:=G) F x).symm.trans
    ((YM.Work.F05.freeEquiv F F').prodCongr (Equiv.refl G.ColorIndex))).trans (Native.lineEquiv F' x)
  have hd : Fintype.card (Active (noHole S) x F × G.ColorIndex) =
      Fintype.card (Active (noHole S) x F' × G.ColorIndex) := Fintype.card_congr he
  unfold chartCost
  rw [hd,Matrix.det_nonsing_inv,Matrix.det_nonsing_inv,
    flat_det T x k F F' k' h hT]

end YM.Integration.PhysicalAffineScalarAperture
end
