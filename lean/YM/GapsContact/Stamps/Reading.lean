import YM.GapsContact.Stamps.Invoice
/-!
# Centered stencil budget for all orientations of actual fields
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Stamps
open Function Filter Set Extraction Extraction.Spin Table Cells OS OS.Ground Lattice Spec MeasureTheory Wilson Trace
open RG Trace.Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb Trace.Verse
open Glyph Next.Rank.Station Next.Rank.Tapes.West Analysis Marker Edition
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d n i: ℕ}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}
local notation "S'"=> Cells.standard C
local notation "A'"=> C.path.levels
local notation "U'"=> (𝓛:Filter (ℕ×ℕ))
variable (hL:𝓛.toFilter ≤ f.fuse) (h:Gondola f H J 𝓛 W Y)
variable (hC:C.Makes) (hG:G.Simple) (v:(Cells.standard C).Field d)
include hL h hC hG
lemma extend_basis :
    ∃ A:ℝ, 0 ≤ A ∧ ∀ᶠ i in atTop, ∀ᶠ u:ℕ×ℕ in U',
    centeredBudget C (held (W:=W) i d u v) A (purchaseWidth (W i)) u.1 u.2 := by
  let b : Module.Basis (PegC C d) ℂ ((S').Field d) := PoleC C d
  choose A ha hv using fun t:PegC C d=> pair_origin hL h hC 1 (by norm_num) one_lt_two hG t
  let y t := b.repr v t; let c:=∑ t:PegC C d, ‖y t‖*A t
  refine ⟨c, Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (ha i), ?_⟩
  filter_upwards [eventually_all.mpr hv] with i hi
  filter_upwards [eventually_all.mpr hi,(link_mesh hL).eventually_ge_atTop (max (C.ref d) (purchaseWidth (W i)))] with u hu he
  have hm:purchaseWidth (W i) ≤ u.1 := (le_max_right ..).trans he
  refine ⟨hm, (le_max_left ..).trans he, fun o=>?_⟩
  let L:=Cells.center C.S u.2 hm o; let β:=C.beta u.1 u.2
  let F:= ((C.linearO u.1 u.2 d o).mk' _).comp (heightV W i d u).toLinearMap
  have hv : v= ∑ t, y t • b t := (b.sum_repr _).symm
  have hx(t:PegC C d): Interior (L.chamber 0) (F (b t)) ∧ L.rootTest β (F (b t)) ≤ A t := (hu t).choose_spec.2 o
  change Interior _ (F v) ∧ L.rootTest _ (F v) ≤ _
  rw [hv,map_sum]; simp only [F.map_smul]
  obtain ⟨hK,hB⟩:= Next.Extract.rooted L β (seamless hC ..) Finset.univ (fun t=>F (b t)) y (fun i _=> (hx i).1)
  exact ⟨hK,hB.trans (Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hx i).2 (norm_nonneg _))⟩

def swing (g:Frame) := if g.2 then (S').conj H.spin d ((S').mirror H.spin d g.1 v) else (S').mirror H.spin d g.1 v

omit hC hG in
lemma commute_frame (g:Frame) : ∀ᶠ i in atTop, ∀ᶠ u:ℕ×ℕ in U',
    Extraction.Spin.token C.book (held (W:=W) i d u v) g=held (W:=W) i d u (swing (H:=H) v g) := by
  filter_upwards [eventually_ge_atTop d] with i hi
  let j: Fin (i+1):=⟨d,Nat.lt_succ_of_le hi⟩
  let V:=W i
  filter_upwards [(show ∀ᶠ x:ℕ×ℕ in f.fuse, ∀ j x', V.wheel.atCut x j ((Cells.standard C).conj H.spin j x')=star (V.wheel.atCut x j x') from (h.season i).1.fares.lift_real).filter_mono hL, (show ∀ᶠ x:ℕ×ℕ in f.fuse,∀ j s v,V.wheel.atCut x j ((Cells.standard C).mirror H.spin j s v)=C.book.mirrorGroup j s (V.wheel.atCut x j v) from (h.season i).1.fares.lift_signed).filter_mono hL] with u hb hs
  obtain ⟨a, - | -⟩:=g
  · change Sigma.mk d (C.book.mirrorGroup d a _) = Sigma.mk d _
    refine congr_arg (Sigma.mk (β:=C.book.Ref) d) ?_
    simp only [swing, Bool.false_eq_true, ↓reduceIte, heightV, dif_pos hi]
    exact (hs j a v).symm
  change Sigma.mk d (star (C.book.mirrorGroup d a _)) = Sigma.mk d _
  refine congr_arg (Sigma.mk (β:=C.book.Ref) d) ?_
  simp only [swing, ↓reduceIte, heightV, dif_pos hi]; exact ((hb j _).trans (congr_arg star (hs j a v))).symm

lemma moving_budget :
    ∃ A:ℝ, 0 < A ∧ ∀ᶠ i in atTop, ∀ᶠ u:ℕ×ℕ in U',
    Next.Phase.Single C (held (W:=W) i d u v) A (purchaseWidth (W i)) u.1 u.2 := by
  choose A ha hv using fun g:Frame=> extend_basis hL h hC hG (swing (H:=H) v g)
  obtain ⟨c,hP,hc⟩ := ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr (fun g => eventually_ge_atTop (A g)))).exists
  refine ⟨c,hP,?_⟩
  filter_upwards [(eventually_all.mpr hv), (eventually_all.mpr (commute_frame hL h v))] with i hb ht
  let k:= purchaseWidth (W i)
  have he₀:∀ᶠ u:ℕ×ℕ in f.fuse, Around.Fit (C:=C) ⟨d,0⟩ k u.1 u.2:= by
    rw [Order.fused]; exact Eventually.of_forall fun _=>(Around.fit _ k).mono fun j hj=> hj _
  filter_upwards [eventually_all.mpr hb,eventually_all.mpr ht, he₀.filter_mono hL] with u hu hh hk
  refine ⟨hk.choose, fun _ g=>?_⟩
  rw [hh]
  exact ⟨fixup C (hu g) (hc g), hk⟩

lemma held_reading :
    ∃ A:ℝ, 0 < A ∧ ∀ᶠ i in atTop,
    OPE.Coverage.Pass.Reading C U' (⟨d,Y d i v⟩:C.book.Token) A (purchaseWidth (W i)) := by
  obtain ⟨A,hA,hB⟩:= moving_budget hL h hC hG v
  refine ⟨A,hA,?_⟩
  filter_upwards [hB,h.terminal d] with i hi hh
  exact ⟨fun t=> heightV W i d t v, Dash.arcing hh.1 (tendsto_const_nhds (x:=v)), hi⟩
end YM.GapsContact.Stamps
