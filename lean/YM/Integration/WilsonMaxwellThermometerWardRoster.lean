import YM.Integration.WilsonMaxwellThermometerWardSocket

/-! Assemble every choice of the previously identified source poles into the
same ordinary finite inversion numerator, with independent source tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardRoster
open Function Finset Lattice Wilson RG Source Labels Marker Next.Rank
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords
open WilsonThermometerDeclaredSeeds WilsonThermometerInversionSockets
open WilsonMaxwellThermometerWardSocket
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)
variable (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (N per:ℕ)
  (o:V→Site (R.family.side N per)) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "gs" => Pert.Asymptotics.regulatorRun R.family N per N
local notation "E" j:max ai:max => entry R d j ai
omit [Fintype V] [DecidableEq V] in
def belongs (e:V→ℕ) (b:(j:V)→Choice R d j):Prop:=∀j,pole R d (E j (b j))=e j

private theorem projection (a:ℝ) (w:ℂ):L (↑a*w)=a*L w:=by
  simpa only [Complex.real_smul,smul_eq_mul] using L.map_smul a w

def marked (e:V→ℕ) (U:Config G (R.family.side N per)):ℝ :=
  L (∏j:V, t j x * (R.family.localSection (d j)).places
    ((R.family.labels.level (d j)).scaled ((R.family.path.rep N per N).p.threshold)⁻¹
     (screen (R.family.labels.level (d j)) (e j) (v j))) (o j) U)

theorem original (e:V→ℕ) (U:Config G (R.family.side N per)):
    (∑b:(j:V)→Choice R d j,
      if belongs R d e b then
        (gs)⁻¹^(charge R d univ b) *
        word R d univ b o (gs) ((R.family.path.rep N per N).p.threshold) v t x L U
      else 0) = marked R d v t N per o x L e U :=by
  classical
  let τ:=(R.family.path.rep N per N).p.threshold
  let f (j:V) (a:Choice R d j):ℂ:=
    if pole R d (E j a)=e j then
      (((gs)^(d j+1):ℝ):ℂ)⁻¹*WilsonThermometerFrozenCopies.word R d (gs) τ v t (E j a) (gs) x (o j) U else 0
  have pair (b:(j:V)→Choice R d j):
      (if belongs R d e b then (gs)⁻¹^(charge R d univ b) * word R d univ b o (gs) τ v t x L U else 0)=
      L (∏j:V,f j (b j)):=by
    by_cases fits:belongs R d e b
    · rw [if_pos fits]
      have sep (j:V):f j (b j)=
          (((gs)^(d j+1):ℝ):ℂ)⁻¹ * WilsonThermometerFrozenCopies.word R d (gs) τ v t (E j (b j)) (gs) x (o j) U :=if_pos (fits j)
      simp_rw [sep]
      rw [prod_mul_distrib]
      simp only [←Complex.ofReal_inv,←Complex.ofReal_prod]
      rw [projection]
      exact (WilsonThermometerInversionFiling.restored R d univ b o (gs) τ v t x L (gs)
        (IterationFour.Currency.g_pos R.makes N per N le_rfl).ne' U).symm
    · rw [if_neg fits]
      obtain ⟨j,wrong⟩:=not_forall.mp fits
      have gone:f j (b j)=0:=if_neg wrong
      rw [prod_eq_zero (mem_univ j) gone,map_zero]
  have data (j:V): (∑a:Choice R d j,f j a)=
      t j x*(R.family.localSection (d j)).places
        ((R.family.labels.level (d j)).scaled τ⁻¹ (screen (R.family.labels.level (d j)) (e j) (v j))) (o j) U:=
    WilsonMaxwellThermometerWardSocket.original R d v t N per o x j (e j) U
  calc
    _=∑b:(j:V)→Choice R d j,L (∏j:V,f j (b j)):=sum_congr rfl fun b _=>pair b
    _=L (∏j:V,∑a:Choice R d j,f j a):=by rw [Fintype.prod_sum,map_sum]
    _=marked R d v t N per o x L e U:=by simp_rw [data];rfl

end YM.Integration.WilsonMaxwellThermometerWardRoster
