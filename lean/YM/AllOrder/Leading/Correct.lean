import YM.TraceExtension.Chart.Time
import YM.Next.UV_STRESS.Focus
import YM.TraceExtension.Atlas.Global

/-!
# Starting the exact normalization: repair the frames at arbitrary real lengths

Use `Pilot.Bliss.picks`, **not** the sparse weak sequence of a matching
receipt. For each sufficiently late tail, on its chosen subsequence the
fields already converge to FREE (leading order), but may not be compatible
from horizon to horizon. Correct using actual & free inclusion maps,
which leaves unchanged the cap-four frame. This preserves the normalization
of the stress of the trace comparison at this stage.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open MergeProof.East Next.UVStress Maxwell
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S}

local notation "free" => Bel C.book
local notation "W" => F.sector.derivatives
local notation "V" => Maxwell.Free.scheme C.labels

set_option maxHeartbeats 200000 in
/-- Adapted from `Stations.equivalences`; additionally shows length and
low frame preservation. The inputs are supplied by the `Scribe` conclusion
of the strengthened trace family. -/
lemma align_seq (hG : G.Simple) {h : (free).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    {J : Scaling S} (hj : StarPath f h J F.room.kernel l) :
    ∃ X : Scaling S, X.r = J.r ∧ Approaches (path X) (isoPanel X) ∧
      Stable F.room.kernel.spin h.spin W V X ∧
      ∀ᶠ i in atTop, X.U i 4 = J.U i 4 := by
  classical
  let U k := isoPanel J k
  let x := path J
  have ha := hj.approach
  let Rw := W
  let H : S.Hierarchy := F.room.kernel
  have hW : Rw.Inclusions S := F.phase.transport.injection
  have hp : Rw.Orientation H.spin := F.phase.transport.rights
  have hV : (V).Inclusions free := Maxwell.Free.scheme_filters ..
  have hf : (V).Orientation h.spin := Maxwell.Free.phase_orientation ..
  choose R hR hb hr using fun d => signed_section (H:=h) (Nat.le_succ d) hV hf
  let Q k := corrected Rw V R (U k)
  have hS (d : ℕ) : ∀ᶠ k in atTop, StraightAt H.spin h.spin (U k) d :=
    (hj.units d).mono fun k hk => ⟨hk.1.stars, hk.1.signed⟩
  have hu d := solid (H:=H) (a:=h) U hp hf R hb hr hS d
  have ha : Approaches x Q := adjusts H h hW hV x R ha
  have he d : ∀ᶠ k : ℕ in atTop, Bijective (Q k d) := by
    filter_upwards [MeterTest.injects H.smooth h ha d] with k hk
    exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (J.U k d).finrank_eq).1 hk⟩
  let M k d := if p : Bijective (Q k d) then LinearEquiv.ofBijective _ p else J.U k d
  let X : Scaling S := {J with U:=M}
  have hX d : ∀ᶠ k in atTop, isoPanel X k d=Q k d := by
    filter_upwards [he d] with k hk
    dsimp only [isoPanel,X,M]; rw [dif_pos hk]; rfl
  have hv (k d e : ℕ) (h' : d≤e) z : Q k e ((V).rise h' z)=Rw.rise h' (Q k d z) :=
    balanced H h _ hW hV R hR d e h' z
  refine ⟨X,rfl,⟨fun n v => ?_⟩,⟨?_,?_,?_⟩,?_⟩
  · refine (ha.values n v).congr (fun k => (smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc h.smooth v)) ?_
    filter_upwards [eventually_all.mpr (fun i : Fin n => hX (v i).1)] with k hk
    intro y _; change tested _ _ _ _ - _ = tested _ _ _ _ - _
    unfold tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel X k) ∘ v from funext (fun i => by
      change Sigma.mk (v i).1 (Q k _ _) = Sigma.mk (v i).1 (isoPanel X k (v i).1 (v i).2)
      rw [hk])]; rfl
  · intro d
    filter_upwards [hX d,hu d] with k hk ht
    constructor
    · intro s p
      change (isoPanel X k d) _= S.mirror _ _ _ ((isoPanel X k d) _)
      rw [hk]; exact ht.reflects ..
    intro p; change (isoPanel X k d) _= S.conj _ _ ((isoPanel X k d) _)
    rw [hk]; exact ht.bars ..
  · intro d e h'
    filter_upwards [hX d,hX e] with k hk he v
    change (isoPanel X k e) _=Rw.rise h' ((isoPanel X k d) _)
    rw [he,hk,hv]
  · intro d
    filter_upwards [hX d,hj.units 0] with k hk hU
    have hh : Q k 0 ((free).unit 0)=S.unit 0 := hU.2
    change (isoPanel X k d) _=_
    let h' := Nat.zero_le d
    rw [hk,← (V).fixs hV h.laws h',hv,hh,Rw.fixs hW H.laws h']
  have hlow (d : ℕ) (hd : d ≤ 4) : ∀ᶠ k in atTop, Q k d = U k d := by
    induction d with
    | zero => exact Eventually.of_forall fun _ => rfl
    | succ d ih =>
      have hl : d<4 := hd
      filter_upwards [ih hl.le,hj.units d,hj.units (d+1)] with k hi hd he
      apply LinearMap.ext; intro v
      change corrected _ _ _ _ _ v = _
      rw [correction]
      change Rw.rise _ (Q k d _) + _ = _
      obtain ⟨c,hc⟩ := UVNext.FreeStress.below C.labels hG hl (R d v)
      have hB : R d v=c • (free).unit d := hc
      have hu0 : U k d ((free).unit d)=S.unit d := hd.2
      have hu1 : U k (d+1) ((free).unit (d+1))=S.unit (d+1) := he.2
      simp_rw [hi,hB,map_sub,map_smul,hu0,(V).fixs hV h.laws,hu1,Rw.fixs hW H.laws]; abel
  filter_upwards [hlow 4 le_rfl,hX 4] with k hi hx
  apply LinearEquiv.toLinearMap_injective
  exact hx.trans hi

end YM.AllOrder.Leading
