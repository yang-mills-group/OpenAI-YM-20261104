import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Geometry
import YM.OPE.Orbits.System
import YM.PhysMS.Frame.Measured
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
/-! # The parent/root scalar line is tested in the *given state* and is common across all.

Exercise `... Size.dim_before` on Bel & use the towers of this same measured horizon,
thus S-rank. Need no subcritical assertions on a schedule or any new properties of P's
actor there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Finset Filter Set MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open Climb PhysMS
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)

lemma observeone_unit (o:E4) (d:ℕ) (v:Viewers F) :
    observeOne S (spectator F v) o (Fin.elim0:Fin 0→E4) (Fin.elim0:Fin 0→C.book.Token) d (S.unit d)=1 := by
  have h : Injective (beside (sole o) (Fin.elim0:Fin 0→E4)) := beside_distinct.mpr ⟨injective_of_subsingleton _,injective_of_subsingleton _,fun _ j=>j.elim0⟩
  unfold Table.unit
  rw [projectedOne _ _ _ _ (spectate F v).laws.toSymmetric (spectate_respects F v) h, show (Sigma.mk d _ : C.book.Token)=_ from rfl];
  exact (local_one_mem (spectator F v) d _ _ (spectate F v).laws h).trans (card_zero_eq _ (spectate F v).laws ..)

abbrev test0 (o:E4) (P:Prescription F.sector.derivatives) (a:Mode F.sector.derivatives) (v:Viewers F) :=
    observe (spectator F v) (beside (sole o) (Fin.elim0 : Fin 0 → E4)) (beside (sole (P.letter a)) (Fin.elim0:Fin 0→C.book.Token))
variable (Z:tower S) (hG:G.Simple)
include F Z hG
lemma line (d : ℕ) (h : d < 4) (z : S.Field d) : ∃ c:ℂ, c • S.unit d=z := by
  have he: Module.finrank ℂ (S.Field d)=1 := (Z d).symm.finrank_eq.trans (UVNext.FreeStress.dim_before C.labels hG h)
  exact (finrank_eq_one_iff_of_nonzero' (S.unit d) (S.alive d F.room.kernel.laws)).1 he z
lemma picked (o:E4) (P:Prescription F.sector.derivatives) (a:Mode F.sector.derivatives) (ha : a.1<4) (v:Viewers F) :
    test0 F o P a v=test0 F 0 P a none := by
  obtain ⟨c,h⟩ := line F Z hG _ ha (S.project a.1 (P.letter a).2)
  have he (o:E4) (v:Viewers F) : test0 F o P a v=c:= by
    let T := spectator F v
    have hi : Injective (beside (sole o) (Fin.elim0: Fin 0→E4)) := beside_distinct.mpr ⟨injective_of_subsingleton _,injective_of_subsingleton _,fun i j=> j.elim0⟩
    have V : test0 F o P a v=_ := (projectedOne T (Fin.elim0:Fin 0→C.book.Token) a.1 (S:=S) (P.letter a).2 (spectate F v).laws.toSymmetric (spectate_respects F v) hi).symm
    rw [V,← h,map_smul]; change _ * observeOne _ (spectator F v) _ _ _ _ _=_; rw [observeone_unit,mul_one]
  rw [he,he]
end YM.OPE.Flash259HorizonFork
