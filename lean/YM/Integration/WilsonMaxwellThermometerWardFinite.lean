import YM.Integration.WilsonMaxwellThermometerWardTable
import YM.Integration.WilsonThermometerInversionMaxwell

/-! Every occupied and proper face of the registered finite prescription is
the sum of the issued physical group readings at its permitted source poles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardFinite
open Function Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open WilsonThermometerInversionSockets WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonMaxwellThermometerWardRoster PertExtension PertExtension.Orb
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)
omit [Fintype V] [DecidableEq V] in
def profile (b:(j:V)→Choice R d j):V→ℕ:=fun j=>pole R d (entry R d j (b j))

def masks:Finset (V→ℕ):=(Finset.univ:Finset ((j:V)→Choice R d j)).image (profile R d)

theorem permitted (simple:G.Simple) {e:V→ℕ} (h:e∈masks R d) (j:V):
    2*e j≤d j ∧ e j≠1:=by
  obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp h
  refine ⟨?_,?_⟩
  · simpa only [profile,site] using WilsonThermometerInversionMaxwell.twice R d (entry R d j (b j))
  · change pole R d (entry R d j (b j)) ≠ 1
    rcases b j with _|s
    · exact Nat.zero_ne_one
    · exact WilsonMaxwellThermometerWardColors.arity simple _ s.1

variable (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (N per:ℕ)
  (o:V→Site (R.family.side N per)) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "gs" => Pert.Asymptotics.regulatorRun R.family N per N
private abbrev threshold (R:Run G) (N per:ℕ):ℝ:=(R.family.path.rep N per N).p.threshold
local notation "τ₀" => threshold R N per

theorem original (h:ℕ) (even:Even (R.family.side N per).val):
    WilsonThermometerInversionFaces.series R d o (gs) (τ₀) v t x L h =
      ∑e∈masks R d,
        Orb.diag (restrictedO (marked R d v t N per o x ((gs)^(∑j:V,e j) • L) e)) ((∑j:V,e j)+h) :=by
  classical
  let A:=(j:V)→Choice R d j
  let f (b:A):=Orb.diag (restrictedO (word R d univ b o (gs) (τ₀) v t x L)) (charge R d univ b+h)
  have one (b:A):(∑e∈masks R d,if belongs R d e b then f b else 0)=f b:=by
    have cond (e:V→ℕ):belongs R d e b ↔ profile R d b=e:=⟨fun h=>funext h,fun h=>congrFun h⟩
    simp_rw [cond]
    simp [masks]
  have real : WilsonThermometerInversionFaces.series R d o (gs) (τ₀) v t x L h = ∑b:A,f b := by
    unfold WilsonThermometerInversionFaces.series
    apply Finset.sum_congr
    · exact congrArg (@Finset.univ A) (Subsingleton.elim _ _)
    · intro b _; rfl
  rw [real]
  calc
    _=∑b:A,∑e∈masks R d,if belongs R d e b then f b else 0:=
      sum_congr rfl fun b _=>(one b).symm
    _=∑e∈masks R d,∑b:A,if belongs R d e b then f b else 0:=sum_comm
    _=_:=sum_congr rfl fun e _=>WilsonMaxwellThermometerWardTable.original R d v t N per o x L e h even

end YM.Integration.WilsonMaxwellThermometerWardFinite
