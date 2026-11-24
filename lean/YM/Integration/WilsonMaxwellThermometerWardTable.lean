import YM.Integration.WilsonMaxwellThermometerWardRoster

/-! Finite normalized coefficients of the complete genuine roster at a fixed
choice of external Laurent poles. Every child keeps its own site and price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardTable
open Function Finset Lattice Wilson RG Source Labels Marker PhysicalNext.Repeat.Legato
open WilsonThermometerInversionSockets WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonMaxwellThermometerWardRoster PertExtension PertExtension.Orb
open scoped BigOperators Classical
variable {G:Gauge} {n:Side}

theorem vacant (even:Even n.val) (q:ℕ):
    Orb.diag (restrictedO (0:Config G n→ℝ)) q=0:=by
  have hp:PreTest (0:Config G n→ℝ):=WilsonMaxwellThermometerWardLinear.zeroField 0
  have h:=congrFun (WilsonMaxwellThermometerWardFiled.added even hp hp) q
  rw [zero_add,Pi.add_apply] at h
  change diagonalWith (tray G) (restrictedO (0:Config G n→ℝ)) q = 0
  linarith

theorem merged {X:Type} (s:Finset X) (f:X → Config G n → ℝ) (hf:∀x,PreTest (f x))
    (even:Even n.val) (q:ℕ):PreTest (∑x∈s,f x) ∧
    Orb.diag (restrictedO (∑x∈s,f x)) q=∑x∈s,Orb.diag (restrictedO (f x)) q:=by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty];exact ⟨WilsonMaxwellThermometerWardLinear.zeroField 0,vacant even q⟩
  | insert a s fresh ih =>
    rw [sum_insert fresh,sum_insert fresh]
    refine ⟨WilsonMaxwellThermometerWardLinear.plus (hf a) ih.1,?_⟩
    exact (congrFun (WilsonMaxwellThermometerWardFiled.added even (hf a) ih.1) q).trans (congrArg (_+·) ih.2)

variable (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)
variable (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (N per:ℕ)
  (o:V→Site (R.family.side N per)) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "gs" => Pert.Asymptotics.regulatorRun R.family N per N
private abbrev threshold (R:Run G) (N per:ℕ):ℝ:=(R.family.path.rep N per N).p.threshold
local notation "τ₀" => threshold R N per

theorem original (e:V→ℕ) (h:ℕ) (even:Even (R.family.side N per).val):
    (∑b:(j:V)→Choice R d j,if belongs R d e b then
      Orb.diag (restrictedO (word R d univ b o (gs) (τ₀) v t x L)) (charge R d univ b+h) else 0) =
    Orb.diag (restrictedO (marked R d v t N per o x ((gs)^(∑j:V,e j) •L) e)) ((∑j:V,e j)+h) :=by
  classical
  let O (b:(j:V)→Choice R d j):=word R d univ b o (gs) (τ₀) v t x L
  let K (b:(j:V)→Choice R d j):Config G (R.family.side N per) → ℝ:=if belongs R d e b then O b else 0
  let w:=∑j:V,e j
  have valid (b:(j:V)→Choice R d j):PreTest (K b):=by
    dsimp only [K];split
    · exact (incoming R d univ b o (gs) (τ₀) v t x L).1
    · exact WilsonMaxwellThermometerWardLinear.zeroField 0
  have grade {b:(j:V)→Choice R d j} (h:belongs R d e b):charge R d univ b=w :=
    sum_congr rfl fun j _=>h j
  have together:(∑b:(j:V)→Choice R d j,K b)=marked R d v t N per o x ((gs)^w •L) e:=by
    funext U
    rw [Finset.sum_apply,←WilsonMaxwellThermometerWardRoster.original]
    apply sum_congr rfl
    intro b _
    by_cases yes:belongs R d e b
    · dsimp only [K,O]
      rw [if_pos yes,if_pos yes,grade yes]
      simp only [word,smul_apply,smul_eq_mul]
      have live: (gs)≠0 := (IterationFour.Currency.g_pos R.makes N per N le_rfl).ne'
      rw [inv_pow]
      field_simp
    · simp [K,yes]
  calc
    _ = ∑b:(j:V)→Choice R d j, Orb.diag (restrictedO (K b)) (w+h):=by
      apply sum_congr rfl
      intro b _
      dsimp only [K]
      by_cases yes:belongs R d e b
      · rw [if_pos yes,if_pos yes,grade yes]
      · rw [if_neg yes,if_neg yes,vacant even]
    _=Orb.diag (restrictedO (∑b:(j:V)→Choice R d j,K b)) (w+h):=(merged univ K valid even _).2.symm
    _= _ :=by rw [together]

end YM.Integration.WilsonMaxwellThermometerWardTable
