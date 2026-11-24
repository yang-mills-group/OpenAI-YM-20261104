import YM.Integration.WilsonThermometerInversionBirth
import YM.Integration.WilsonMaxwellThermometerWardLinear

/-! Read each deployed Laurent pole of the actual issued original Wilson
source independently, retaining its phase, field, site and chosen inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardSocket
open Function Finset Lattice Wilson RG Source Labels Marker Next.Rank
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneRead ActualRunPhysicalPages
open scoped Classical BigOperators
variable {G:Gauge} {D:ℕ}

def screen (F:Frame G D) (e:ℕ) (v:F.Coeff):F.Coeff:=fun b=>if (F.grades b).2=e then v b else 0

private theorem clean (F:Frame G D) (e:ℕ) (v:F.Coeff) (b:F.Index):
    F.core (screen F e v) b=if (F.grades b).2=e then F.core v b else 0:=by
  by_cases h:b=0
  · subst b
    simp [Frame.core]
  · simp [Frame.core,Function.update,screen,h]

variable (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)
variable (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ)
local notation "F" j => R.family.labels.level (d j)
local notation "Q" e => fun j=>screen (F j) e (v j)

omit [Fintype V] [DecidableEq V] in
theorem fiscal (g τ:ℝ) (e:ℕ) (i:Entry R d):
    scalar R d g τ (Q e) i =
      if pole R d i=e then scalar R d g τ v i else 0:=by
  rcases i with j|⟨j,b,s⟩
  · simp [scalar,pole,screen,(F j).zero_degree]
  · change _ * ((F j).core (screen (F j) e (v j)) b) * _ =
      if ((R.family.labels.level (d j)).grades b).2=e then _ else 0
    rw [clean]
    by_cases he: ((R.family.labels.level (d j)).grades b).2=e
    · simp only [if_pos he]
      rfl
    · simp only [if_neg he,mul_zero,zero_mul]

variable (N per:ℕ) (o:V→Site (R.family.side N per)) (x:T)
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per N
private abbrev threshold (R:Run G) (N per:ℕ):ℝ:=(R.family.path.rep N per N).p.threshold
local notation "τ" => threshold R N per

private theorem receipt (i:Entry R d) (U:Config G (R.family.side N per)):
    (((g)^(d (root R d i)+1):ℝ):ℂ)⁻¹*
      WilsonThermometerFrozenCopies.word R d (g) (τ) v t i (g) x (o (root R d i)) U =
        (rows R d o 1 (g) (τ) v t i).nominal (g) x U := by
  have live: (g)≠0 := (IterationFour.Currency.g_pos R.makes N per N le_rfl).ne'
  rw [WilsonThermometerFrozenRevaluation.at_birth R d (g) (τ) v t i x (o (root R d i)) U live,
    nominal,WilsonThermometerFrozenSockets.separated R d (g) (τ) v i]
  have e (a:ℕ) : (g)^(-(a:ℤ)) * ((g)/(τ))^a = (τ)⁻¹^a := by
    rw [zpow_neg,zpow_natCast,←inv_pow,←mul_pow,div_eq_mul_inv,←mul_assoc,inv_mul_cancel₀ live,one_mul]
  have eq:=congrArg Complex.ofReal (e (pole R d i))
  simp only [Complex.ofReal_mul,Complex.ofReal_zpow] at eq
  linear_combination -(t (root R d i) x * scalar R d 1 1 v i * ↑((raw R d i).unmasked U (o (root R d i)))) * eq

theorem original (j:V) (e:ℕ) (U:Config G (R.family.side N per)):
    (∑ ai:Choice R d j, if pole R d (entry R d j ai)=e then
      (((g)^(d j+1):ℝ):ℂ)⁻¹ *
        WilsonThermometerFrozenCopies.word R d (g) (τ) v t (entry R d j ai) (g) x (o j) U
      else 0) =
      t j x * (R.family.localSection (d j)).places ((F j).scaled (τ)⁻¹ (screen (F j) e (v j))) (o j) U :=by
  have clip (ai:Choice R d j) :
      (if pole R d (entry R d j ai)=e then (((g)^(d j+1):ℝ):ℂ)⁻¹ *
       WilsonThermometerFrozenCopies.word R d (g) (τ) v t (entry R d j ai) (g) x (o j) U else 0)=
        (rows R d o 1 (g) (τ) (Q e) t (entry R d j ai)).nominal (g) x U :=by
    have atSite:=receipt R d v t N per o x (entry R d j ai) U
    simp only [site] at atSite
    rw [atSite,nominal,nominal,fiscal]
    split <;> simp_all only [mul_zero,zero_mul]
  simp_rw [clip]
  rw [Fintype.sum_sum_type,Fintype.sum_unique]
  change (rows R d o 1 (g) (τ) (Q e) t (.inl j)).nominal (g) x U+
      ∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),
        (rows R d o 1 (g) (τ) (Q e) t (.inr ⟨j,s⟩)).nominal (g) x U=_
  rw [scalar_read,monomials R d 1 (Q e) t N per N le_rfl o j x U,←mul_add]
  exact congrArg (fun z:ℂ=>t j x*z)
    (WardBin.write_unitpart (R.family.localSection (d j)) (R.makes.sections (d j)) (τ)
        (screen (F j) e (v j)) (expandAt (o j) U)).symm

end YM.Integration.WilsonMaxwellThermometerWardSocket
