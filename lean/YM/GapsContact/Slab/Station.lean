import YM.GapsContact.Stamps.Reading
import YM.GapsContact.Stamps.Overhang
import YM.Work.C01
/-!
# Actual short slab estimate before propagation in length

Uses Wilson data of the Trace construction through `Gondola`. Uses the **same** subfilter
of cutoff mesh/period ordered limits as there for all these estimates. Funds the operator power
argument with the full stamped arrays. Outputs budget uniform in time widths satisfying the
lossy bound using `LogZoom`. All positions can be translated/padded with fixed buffers to use
these estimates. Materialized here on the centered insertions for propagation to the complex
time kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Ascent
open Function Filter Set Extraction Table Cells OS Lattice Spec MeasureTheory Wilson Trace
open RG Trace.Terrace Trace.Over MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Stamps Boundary
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff

section invariant
variable {G : Gauge} {L : Register G} {S T : Table L} {V : OS.Chamber T timeAxis}
variable {A : Spread V} {d : ℕ} {x : L.Ref d} {p : ℝ≥0}

open Work.C01
lemma place_raw (h : T.Symmetric) (hT : T.respects S) (hp : 0 < p):
    A.place (p+p) [Work.C01.center p (⟨d,x⟩:L.Token)] = single A h hp d (S.project d x) := by
  apply op_ext; intro v w
  rw [inner_raw _ h hp]
  change _ = inner ℂ (V.GNS.plant v) (A.place (p+p) [Work.C01.center p (Ward.expose (⟨d,S.project d x⟩:S.Tag))] _)
  rw [inner_quotient A h hT hp]
  have he : Points.cons (position 0 p) (Word.positions (spectators p v w)) ∈ conf _ := Ward.disjoint_table (cleared (⟨d,x⟩:L.Token) hp v w)
  rw [← S.at_project T h hT he]; congr 1
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
lemma small_field (B : Small S V)(hB:B.concretized A)(h : T.Symmetric) (hp : 0 < p) (x:S.Field d) :
    B.bar p (S.pin d x)=single A h hp d x:= hB d _ p hp
end invariant

variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d n i: ℕ}
variable (F : Final C f S)
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}
local notation "S'"=> Cells.standard C
local notation "C'"=> C.path.levels
variable (hL:𝓛.toFilter ≤ f.fuse) (h:Gondola f H J 𝓛 W Y) (θ: PostT C.path.levels) (hG:G.Simple) (v:(Cells.standard C).Field d)
local notation "I"=> Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric

include F θ hG h hL
lemma one_field :
    ∃ A:ℝ, 0 < A ∧ ∀ᶠ i in atTop,
      ∀ p : ℝ≥0, ∀ hp : 0 < p, J.r i*LogZoom J i ≤ p → ‖I hp d (J.U i d v)‖ ≤ A := by
  obtain ⟨A,hA,hB⟩:= held_reading hL h F.room.cutoff hG v
  refine ⟨A,hA,?_⟩
  filter_upwards [hB,h.terminal d, overhang h hG θ] with i hi hm ⟨hk,hN,hS⟩ p hp hl
  let x := Y d i v; let t : C.book.Token:=⟨d,x⟩; let w:= purchaseWidth (W i)
  have hs:C.S.a (w-1) < (p:ℝ)/32 := hS.trans_le (by gcongr)
  have hv:= OPE.Coverage.funded F.room.cutoff F.room.generic F.room.kernel F.room.copies _ hL hs (k:=w) (Nat.sub_le ..) hN hi hA
  let M:= F.α.unselected
  obtain ⟨P,hP,h'⟩ := hv.ride F.α.room (position 0 p) (p+p) (Work.C01.centeredSlab p t hp) (Work.C01.centeredBuffer p t)
  have hX:P=M.place (p+p) [Work.C01.center p t] := F.α.room.GNS.by_bud fun y=> (h' y).trans (M.reads (Work.C01.centeredSlab p t hp) y).symm
  rw [hX,place_raw (S:=S) F.room.kernel.laws.toSymmetric (fun _=> le_rfl) hp] at hP
  rw [hm.2 v]; exact hP

lemma basis_field (d:ℕ) :
    ∃ A:ℝ, 0 ≤ A ∧ ∀ᶠ i in atTop,
      ∀ p : ℝ≥0, ∀ hp : 0 < p, J.r i*LogZoom J i ≤ p → ∀ v:(Cells.standard C).Field d,
        ‖I hp d (J.U i d v)‖ ≤ A * ‖v‖ := by
  choose A hA hB using fun t : PegC C d=> one_field F hL h θ hG (PoleC C d t)
  let K: Module.Basis (PegC C d) ℂ ((S').Field d) := PoleC C d
  let a(t:PegC C d):= (K.coord t).toContinuousLinearMap
  let c := ∑ t: PegC C d, ‖a t‖*A t
  refine ⟨c,Finset.sum_nonneg fun i _=> mul_nonneg (norm_nonneg (a i)) (hA i).le,?_⟩
  filter_upwards [eventually_all.mpr hB] with i hi p hp hx v
  let f:= (I hp d).comp (J.U i d).toLinearMap
  change ‖f v‖ ≤ _
  conv_lhs => rw [← K.sum_repr v,map_sum]
  simp_rw [f.map_smul]
  refine (norm_sum_le _ _).trans ?_
  unfold c; rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _=> ?_
  rw [norm_smul, mul_right_comm _ _ ‖v‖]; exact mul_le_mul ((a j).le_opNorm v)
    (hi j p hp hx) (norm_nonneg _) (mul_nonneg (norm_nonneg (a j)) (norm_nonneg v))

end YM.GapsContact.Ascent
