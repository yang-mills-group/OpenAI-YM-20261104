import YM.GradedFar.Logged.GrowingStage
import YM.OPE.Short.Vacuum
import YM.RG12.Canonical.Low

/-!
# Degree-zero root estimate, all viewer phases

Adaptation (up to center placement which is arbitrary) of
`Integration/WilsonThermometerWeakPairViewerVacuum.canonical,common`.
No Scaling assumed here. `algebra` estimates used by subsequent price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.VAC
open Function Filter Finset Set Spec Table Extraction OPE OPE.Orbits OPE.Log OPE.Arboreal OPE.Nesting
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I:Type}{P:Prescription F.sector.derivatives}
local notation "bare"=> Stage.bare
abbrev blanks{S:Table C.book} := (fun v:Empty=> (Short.extra (z:=v):S.Tag))
-- take root zero grade value shared (use as constant)
def value (F:Final C f S) (P:Prescription F.sector.derivatives) (a:Mode F.sector.derivatives) := pickOne P S (sole 0) () a (bare:Fin 0 → E4) bare

lemma canonical (o:E4) (q:Viewers F)(a:Mode F.sector.derivatives) :
    pickOne P (spectator F q) (sole o) () a (bare:Fin 0 → E4) bare=
      Orbits.upon (spectator F q) a.fst o Short.gapPos (voices (blanks (S:=S))) (P.needle a) := by
    let e:Fin 0 ≃ Empty:=⟨Fin.elim0,Empty.elim,fun i=>Fin.elim0 i,fun i=>nomatch i⟩
    let x:=beside (sole o) Short.gapPos
    let v:=beside (sole (P.letter a)) (Orbits.names (voices (blanks (S:=S))))
    have hx:Injective x:=beside_distinct.mpr ⟨injective_of_subsingleton _,injective_of_subsingleton _,fun _ j=>nomatch j⟩
    have eq:=perm_observe (spectator F q) (spectate F q).laws.toSymmetric (Equiv.sumCongr (Equiv.refl Unit) e) v hx
    change observe _ _ _ = Orbits.whole _ (sole o) (sole (P.needle a)) _ _
    rw [Orbits.whole_observed]
    convert eq using 2 <;> funext i <;> cases i with
    | inl i=>rfl
    | inr i=> exact isEmptyElim i

lemma common (simple:G.Simple)(q:Viewers F) [Fintype I](a:Mode F.sector.derivatives)(x:I→E4)(i:I)(zero:a.fst=0) :
    pickOne P (spectator F q) x i a (bare:Fin 0→E4) bare=value F P a:=by
    change pickOne P (spectator F q) (sole (x i)) () a (bare:Fin 0→E4) bare=pickOne P (spectator F none) (sole 0) () a (bare:Fin 0→E4) bare
    rw [canonical,canonical]
    rcases a with ⟨d,j⟩; change d=0 at zero; subst d
    let z:S.Field 0:= P.needle ⟨0,j⟩; obtain ⟨c,h⟩:= RG12.unit_spans simple C 0 (C.ref 0) (by norm_num) (S.representative 0 z)
    have hz:z=c•S.unit 0:=by rw [←S.rep 0 z,h,map_smul];rfl
    change Orbits.upon (spectator F q) 0 (x i) _ _ z=Orbits.upon (spectator F none) 0 0 _ _ z
    rw [hz,map_smul,map_smul]
    exact congrArg (c • ·) ((Short.vacuum F q (x i) 0 (blanks (S:=S))).trans (Short.vacuum F none 0 0 (blanks (S:=S))).symm)

lemma difference (simple:G.Simple)(q:Viewers F)[Fintype I](b:Finset I)(x:I→E4)(p:I→C.book.Token)(i:I) :
    flux P (spectator F q) b x p i (bare:Fin 0→E4) bare 0 =
      Arboreal.whole (spectator F q) b x p (bare:Fin 0→E4) bare- ∑ w∈bands F.sector.derivatives 0,coalesce P b x p i w * value F P w :=by
    rw [flow_eq]; congr 1; refine Finset.sum_congr rfl fun w hw=>?_ ; rw [common F simple q w x i (Nat.eq_zero_of_le_zero ((full_bands ..).mp hw))]
end YM.OPE.Logged.VAC
