import YM.AllOrder.FrameCost.Levy

/-!
# All-character leading AND phase-flat comparison on separated shapes

`g^-C` costs can be paid out of the exponential physical power margin.
Macroscopic spectator insertions in the exact OPE balance estimate not scaled
with the weak path. Formal positive-output coefficient uses will be separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Next.UVStress Maxwell OPE OPE.Orbits FrameCost OPE.Nesting
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {I J : Type} [Fintype I] [Fintype J] {d : I→ℕ} {e : J→ℕ}

def placed (U : ℝ → FamilyFrame S) (v : (i:I) → (Bel C.book).Field (d i)) (r : ℝ) (i:I) := U r (d i) (v i)
def moments (F : Final C f S) (U : ℝ → FamilyFrame S) (v : (i:I) → (Bel C.book).Field (d i))
    (r : ℝ) (x : I → E4) (o:E4) (q : Viewers F) : ℂ := Orbits.moment (spectator F q) (Short.harmonic r x o) (placed U v r)
def scalarChannel (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : ℝ → FamilyFrame S) (v : (i:I) → (Bel C.book).Field (d i)) (r : ℝ) (x : I → E4) (o:E4) : ℂ :=
    Short.scalar F R (Short.harmonic r x o) (fun i=>⟨d i,placed U v r i⟩) o

variable (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {M η c : ℝ}
variable (v : (i:I) → (Bel C.book).Field (d i)) (w : (i:J)→ S.Field (e i))
variable (h : Aligned F g U) (hF : Services C f S) (hG : G.Simple)
include h hF
lemma remainder (hc : 0<c) (hη : 0<η) (D : ℕ) (b : ℝ)(hb : -(D+1:ℝ)<b) :
    ∀ᶠ r in trail, ∀ (q:Viewers F) (x:I→E4)(o:E4)(y:J→E4),WithinRoom r M η x o → ClearOf o y c →
        ‖balance F (spectator F q) R D x o (placed U v r) y w‖ ≤ Real.exp (b*FrameCost.clock r) :=
    FrameCost.of_sampling (fun X=> Levy.uniform (U:=F) R (sample U X) (anchorage h X) hF hη hc v w D b hb)

omit hF in
lemma unselected_plate (hη : 0<η) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in trail, ∀ x∈ Short.plate I M η, ∀ o:E4,
        ‖moments (d:=d) F U v r x o none-Levy.freeSlots (C:=C) (d:=d) v x‖ < ε := by
    let t : Fin (Fintype.card I)→ (Bel C.book).Tag := Orbits.tags v ∘ runNames I
    have hZ:=compact_zero h t he (K:=Short.frame '' Short.plate I M η)
                  ((Short.meal I M η).image Short.framed.continuous)
                  (Set.image_subset_iff.mpr (fun i hi=> Short.occupancy _ (Short.plate_conf hη _ hi)))
    filter_upwards [hZ,show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin] with r hr hv x hx o
    have hf : moments (d:=d) F U v r x o none = tableRead (U r) r t (Short.frame x) := by
       let x':=fun i=>r • x i
       unfold moments Short.harmonic
       exact (Orbits.carrying (a:=(placed U v r)) (S:=S) F.room.kernel (show Injective x' from (smul_right_injective E4 hv.ne').comp (Short.plate_conf hη _ hx)) o).trans rfl
    rw [hf]; exact hr _ (Set.mem_image_of_mem Short.frame hx)
include hG
-- survives all finite inverse coupling powers
lemma scalar_flat (hη : 0<η) (δ : ℝ) (he : (-1:ℝ)<δ) : ∀ᶠ r in trail,∀ x∈ Short.plate I M η, ∀ (o:E4)(q:Viewers F),
    ‖moments (d:=d) F U v r x o q - scalarChannel (d:=d) F R U v r x o‖ ≤ Real.exp (δ*FrameCost.clock r) := by
    refine FrameCost.of_sampling fun X=> ?_
    have hV:= remainder (M:=M) R v (w:=voices (fun z:Empty => Short.extra (S:=S) (z:=z))) h hF zero_lt_one hη 0 δ (by norm_num; exact he)
    filter_upwards [(sample_trail X).eventually hV] with k hw x hx o q
    let y:=Short.harmonic (X.r k) x o
    let v'(i:I):S.Tag:=⟨d i,(placed U v (X.r k)) i⟩
    have hcl:ClearOf o Short.gapPos 1:= ⟨(fun i=>nomatch i),(fun i=>nomatch i)⟩
    let s:= sample U X
    have hΔ := Short.identity_formula F R s hG y v' o q (Short.injective_harmonic s hη _ _ hx k)
    specialize hw q y o Short.gapPos (Short.fitted hη (X.positive k).le x o hx) hcl
    change ‖Orbits.balance F (spectator F q) R 0 y o (voices v') Short.gapPos (voices (fun z:Empty=> Short.extra (S:=S) (z:=z)))‖≤_ at hw
    rw [Orbits.tested_fields,← Orbits.formula, hΔ] at hw
    exact hw

lemma plate (hη : 0 < η) {ε : ℝ} (he : 0<ε) : ∀ᶠ r in trail, ∀ x ∈ Short.plate I M η, ∀ (o:E4)(q:Viewers F),
    ‖moments (d:=d) F U v r x o q - Levy.freeSlots (C:=C) (d:=d) v x‖ < ε ∧ ‖scalarChannel (d:=d) F R U v r x o - Levy.freeSlots (C:=C) (d:=d) v x‖ < ε := by
    let δ:=ε/4; have hp:0<δ:=div_pos he (by norm_num)
    have ht : Tendsto (fun r=> Real.exp (-(1/2:ℝ)*FrameCost.clock r)) trail (𝓝 0) := Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by norm_num) FrameCost.clock_time)
    filter_upwards [unselected_plate (M:=M) v h hη hp,scalar_flat (M:=M) R v h hF hG hη (-(1/2:ℝ)) (by norm_num), ht.eventually (gt_mem_nhds hp)] with r hU hδ ht x hx o q
    have hw (q:Viewers F) : ‖moments (d:=d) F U v r x o q - scalarChannel (d:=d) F R U v r x o‖ < δ := (hδ _ hx o q).trans_lt ht
    have hh: ‖scalarChannel (d:=d) F R U v r x o-Levy.freeSlots (C:=C) (d:=d) v x‖ < δ+δ := calc
       _ ≤ _:= norm_sub_le_norm_sub_add_norm_sub _ (moments (d:=d) F U v r x o none) _
       _ < _:= add_lt_add ((norm_sub_rev (scalarChannel F R U v r x o) (moments F U v r x o none)).trans_lt (hw none)) (hU _ hx o)
    have hK : δ+(δ+δ) ≤ ε := by unfold δ; linarith only [he]
    exact ⟨((norm_sub_le_norm_sub_add_norm_sub _ (scalarChannel (d:=d) F R U v r x o) _).trans_lt (add_lt_add (hw q) hh)).trans_le hK,
       hh.trans_le ((le_add_of_nonneg_left hp.le).trans hK)⟩

end YM.AllOrder.Leading
