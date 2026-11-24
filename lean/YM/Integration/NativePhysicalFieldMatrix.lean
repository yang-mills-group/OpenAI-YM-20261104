import YM.Integration.OPEPanelAction
import YM.FVAAlt2.First.Tent

/-! The original physical field matrix in the named moving detector basis,
and its action on the complete complex smeared panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativePhysicalFieldMatrix

open Function PowerSeries FVA2 FVA2.Verne FVA2.WorldJet FVA2.PayAll
open Pert.Position PositionX PositionX.Jet RG11.Jets
open FormalOPE.RG10.Position
open scoped BigOperators Classical

variable {G : Gauge} {F : Labels.Frames G} {d n : ℕ}
local notation "I" d => FormalOPE.RG10.Position.Deck F d

/-- Each positive coefficient is the actual buffer operator in the original
RG10 basis. The diagonal zero-order term is the identity field. -/
def field (p : Hop F) (d : ℕ) : Matrix (I d) (I d) (PowerSeries ℝ) :=
  fun i j => mk fun k => (if k = 0 then (1 : Matrix (I d) (I d) ℝ) i j else 0) +
    YM.FVAAlt2.First.Tent.ticket (p.Z.wire d k) i j

theorem entry (p : Hop F) (d : ℕ) (i j : I d) :
    WorldJet.style F (p.Z.wire d) (deck F d) j ((deck F d) i) = deposit (field p d i j) := by
  apply PowerSeries.ext
  intro k
  change Clock.out (WorldJet.style F (p.Z.wire d) (deck F d) j ((deck F d) i)) k = _
  rw [WorldJet.node4, Counterpart.frame_at, map_add, deposited, field, coeff_mk,
    Complex.ofReal_add, YM.FVAAlt2.First.Tent.ticket_r, add_comm]
  by_cases hk : k = 0 <;> by_cases h : i = j <;>
    simp [hk, h, Matrix.one_apply, Module.Basis.coord_apply]
  · rw [← deckAt, Module.Basis.repr_self, Finsupp.single_eq_same]
  · rw [← deckAt, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm h)]

theorem constant (p : Hop F) (d : ℕ) : (field p d).map constantCoeff = 1 := by
  ext i j
  rw [Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply, field, coeff_mk,
    if_pos rfl, show p.Z.wire d 0 = 0 from p.tangent d]
  simp [YM.FVAAlt2.First.Tent.ticket]

theorem determinant (p : Hop F) (d : ℕ) : IsUnit (field p d).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  change IsUnit ((field p d).map constantCoeff).det
  rw [constant, Matrix.det_one]
  exact isUnit_one

def scheme (p : Hop F) (d : ℕ) : Change ℝ (I d) := ⟨mk p.f, field p d⟩

theorem anchored (p : Hop F) (d : ℕ) : Anchored (scheme p d).g := by
  rw [Anchored, ← coeff_zero_eq_constantCoeff_apply]
  change coeff 0 (mk p.f) = 0
  rw [coeff_mk]
  exact p.rooted

abbrev allowance (F : Labels.Frames G) (d : ℕ) : Constraints ℝ (FormalOPE.RG10.Position.Deck F d) :=
  Constraints.filter (FormalOPE.RG10.Position.Deck.price F d)

/-- The real change on the physical deck preserves the original horizon
filtration, including its finite inverse. -/
theorem good (p : Hop F) (d : ℕ) : Change.Good (allowance F d) (scheme p d) := by
  refine ⟨⟨anchored p d, ?_⟩, ⟨?_, ?_⟩⟩
  · change IsUnit (coeff 1 (mk p.f))
    rw [coeff_mk, p.primary]
    exact isUnit_one
  · change piece 0 (field p d) = 1
    ext i j
    change coeff 0 (field p d i j) = _
    rw [coeff_zero_eq_constantCoeff_apply]
    exact congrFun (congrFun (constant p d) i) j
  · intro k hk i j hij
    change coeff k (field p d i j) = 0
    rw [field, coeff_mk, if_neg hk.ne', zero_add]
    exact YM.FVAAlt2.First.Tent.tic_lower (p.Z.wire d k) i j hij

abbrev Datum (F : Labels.Frames G) (d : ℕ) := YM.FVAAlt2.Home.Datum (FormalOPE.RG10.Position.Deck F d)

def series (P : Panel F) (d : ℕ) (v : Datum F d) : PowerSeries ℂ :=
  mk fun k => P.lives d k v.1.n v.1.test (deck F d ∘ v.2)

private theorem named_drag (z : ℕ → Buffer F d) (f : PayAll.reprK F d n)
    (v : Fin n → E F d) :
    mk (fun k => heated f z k v) =
      ∑ u : Fin n → I d, (∏ i, WorldJet.style F z (deck F d) (u i) (v i)) *
        mk (fun k => f k (deck F d ∘ u)) := by
  let t : Test n := 0
  let w := keynote ∘ f
  have hh (k : ℕ) : JetB F (w k) (OPEPanelAction.seriesForm f) t k := by
    change ploy t (keynote (f k)) = _
    rw [heap]
    ext1 x
    change f k x = coeff k (OPEPanelAction.seriesForm f x)
    rw [OPEPanelAction.seriesForm_apply, coeff_mk]
  have he : mk (fun k => heated f z k v) =
      WorldJet.drag F z (deck F d) (OPEPanelAction.seriesForm f) v := by
    apply PowerSeries.ext
    intro k
    rw [coeff_mk, WorldJet.drag_h F z (deck F d) t w v hh]
    rfl
  rw [he, WorldJet.atDrag]
  simp only [OPEPanelAction.seriesForm_apply]

private theorem named_action (p : Hop F) (f : PayAll.reprK F d n) (v : Fin n → I d) :
    mk (fun k => heated (Jet.ren p.f f) (p.Z.wire d) k (deck F d ∘ v)) =
      ∑ u : Fin n → I d, (PowerSeries.subst (deposit (mk p.f)) (mk (fun k => f k (deck F d ∘ u)))) *
        ∏ i, deposit (field p d (v i) (u i)) := by
  rw [named_drag]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Function.comp_apply, entry, mul_comm (∏ i, _)]
  apply congrArg (· * _)
  change mk (taste (Jet.ren p.f f) (deck F d ∘ u)) = _
  rw [PayAll.value_ren, OPEPanelAction.renormalized p]

/-- The field and coupling action is computed on the literal named detector
with the same test and every independently chosen input. -/
theorem forward (P : Panel F) (hP : P.clearP) (p : Hop F) (d : ℕ) (v : Datum F d) :
    series (Hop.act P p) d v = (toComplex (scheme p d)).act (series P d) v := by
  let f : PayAll.reprK F d v.1.n := ploy v.1.test ∘ P.lives d
  have ht (k : ℕ) : (Hop.act P p).lives d k v.1.n v.1.test (deck F d ∘ v.2) =
      heated (Jet.ren p.f f) (p.Z.wire d) k (deck F d ∘ v.2) := by
    rw [Hop.act, Panel.turn_book _ _ (Panel.bright P p.f hP), Panel.total_book P p.f hP]
    exact (DFunLike.congr_fun (PayAll.myTip (Jet.ren p.f f) (p.Z.wire d) k v.1.test
      (Jet.ren p.f (P.lives d)) (ren_writes (ploy v.1.test) p.f (P.lives d))) (deck F d ∘ v.2)).symm
  change mk (fun k => (Hop.act P p).lives d k v.1.n v.1.test (deck F d ∘ v.2)) = _
  simp_rw [ht]
  exact named_action p f v.2

theorem component_action (L : ℂ →ₗ[ℝ] ℝ) (P : Panel F) (hP : P.clearP) (p : Hop F)
    (d : ℕ) (v : Datum F d) :
    part L (series (Hop.act P p) d v) = (scheme p d).act (fun u => part L (series P d u)) v := by
  rw [forward P hP]
  exact (part_transform L _ _ (anchored p d) v).symm

end YM.Integration.NativePhysicalFieldMatrix
end
