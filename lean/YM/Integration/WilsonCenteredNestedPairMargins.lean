import YM.Integration.WilsonCenteredNestedPairConvoy
import YM.Integration.WilsonCenteredNestedTicketSites
import YM.Integration.WilsonCenteredNestedRootMean

/-! A single physical exit-sheet margin for both independently placed near
positions and the far actor. It holds even as the two near positions coalesce. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairMargins
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairConvoy
open WilsonCenteredNestedTicketSites
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

lemma fits {M η r a:ℝ} {z:full.Plot} (ok:Accept r M η (dates r a) z) :
    ∀i,‖trio (sites z) i-sites z 0‖≤M*r := by
  have rel:=ok.relative
  intro i
  fin_cases i
  · exact rel.1 (.inr ⟨0,.inr ⟨0,()⟩⟩)
  · exact rel.1 (.inr ⟨0,.inr ⟨1,()⟩⟩)
  · exact rel.1 (.inr ⟨1,()⟩)

lemma distinct {M η r a:ℝ} {z:full.Plot} (ηp:0<η) (ok:Accept r M η (dates r a) z) :
    Injective (trio (sites z)) := by
  have near := ok.relative.2.2 (0:Fin 2)
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have rp := ok.levels.1
  have xy : η*a ≤ ‖sites z 2-sites z 3‖ := near.2.1 (0:Fin 2) 1 () () (by decide)
  have xf : η*r ≤ ‖sites z 2-sites z 4‖ :=
    ok.relative.2.1 (0:Fin 2) 1 (.inr ⟨0,()⟩) (arms 1).topSeat (by decide)
  have yf : η*r ≤ ‖sites z 3-sites z 4‖ :=
    ok.relative.2.1 (0:Fin 2) 1 (.inr ⟨1,()⟩) (arms 1).topSeat (by decide)
  have pq := sub_ne_zero.mp (norm_pos_iff.mp ((mul_pos ηp ap).trans_le xy))
  have pf := sub_ne_zero.mp (norm_pos_iff.mp ((mul_pos ηp rp).trans_le xf))
  have qf := sub_ne_zero.mp (norm_pos_iff.mp ((mul_pos ηp rp).trans_le yf))
  intro i j he
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact (pq he).elim
    | exact (pf he).elim
    | exact (qf he).elim
    | exact (pq he.symm).elim
    | exact (pf he.symm).elim
    | exact (qf he.symm).elim

theorem original (m:ℕ) (M η:ℝ) (ηp:0<η) :
    ∀ᶠr:ℝ in 𝓝[>]0,∀ (a:ℝ)(z:full.Plot),Accept r M η (dates r a) z →
      orbitMargin Q.port m (trio (sites z)) (sites z 0) := by
  have clock : Tendsto (fun r:ℝ=>M*r) (𝓝[>]0) (𝓝 (M*0)) :=
    ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
  have good (j:Mode F.sector.derivatives) (e:Exterior C.book) (_he:e∈(Q.port.sheet j).support) (u:Fin e.n) :
      ∀ᶠ r:ℝ in 𝓝[>]0,M*r<‖bearing e u‖ := by
    have bearingPos := norm_pos_iff.mpr (Ne.symm ((beside_distinct.mp (bearing_clear e)).2.2 () u))
    exact clock.eventually (eventually_lt_nhds (by simpa using bearingPos))
  filter_upwards [(eventually_all_finset (bands F.sector.derivatives m)).mpr (fun j _=>
    (eventually_all_finset (Q.port.sheet j).support).mpr (fun e he=>eventually_all.mpr (good j e he)))] with r bound a z ok j hj k e he
  refine beside_distinct.mpr ⟨(away_inject _ _).mpr ((Ortho.motion k).injective.comp (distinct ηp ok)),
    (beside_distinct.mp (bearing_clear e)).2.1,fun i u hi=>?_⟩
  have hv:‖away (Ortho.move k ∘trio (sites z)) (Ortho.move k (sites z 0)) i‖=‖trio (sites z) i-sites z 0‖ :=
    (congr_arg norm (show _=Ortho.motion k (trio (sites z) i-sites z 0) from (map_sub (Ortho.motion k) _ _).symm)).trans
      (LinearIsometryEquiv.norm_map _ _)
  exact ((fits ok i).trans_lt (bound j hj e he u)).ne (hv.symm.trans (congr_arg norm hi))

end YM.Integration.WilsonCenteredNestedPairMargins
