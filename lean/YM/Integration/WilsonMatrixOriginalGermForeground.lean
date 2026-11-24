import YM.Integration.WilsonReportRootedPartners
import YM.Integration.WilsonMatrixOriginalGermGram

/-! Price the complete signed forced numerator in an actual earlier field, at its translated
anchor. The denominator is the original nonbare compatible gas. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermForeground
open Finset MeasureTheory Lattice Wilson RG Source Labels MergeProof Push.Local
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph Next.Rank.Price
open WilsonInheritedRegisteredField ActualWilsonExteriorPrice SectorNext.Vacuum
open private anchor from YM.Integration.WilsonMatrixOriginalGermAnchor
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {m N p:ℕ}

def vacuum (m N p:ℕ) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):ℝ :=
  let A:=R.family.path.rep N p m
  A.activities.gas A.p (pull 1 o U)

def weight (m N p:ℕ) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):ℝ :=
  let A:=R.family.path.rep N p m
  let F:=flags A.p.threshold (pull 1 o U)
  if F=∅ then 0 else Real.exp (-flagRate A.p*F.card)

theorem solvent (live:m ≤ N) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    0<vacuum R m N p o U:=by
  let V:=pull (1:Signed) o U
  let A:=R.family.path.rep N p m
  have pos:0<A.eval V:=Multi.AxisShift.chosen_positive R.makes.wilson live V
  exact pos_of_mul_pos_right pos (Real.exp_pos (A.exponent V)).le

private theorem billed (age:R.family.ref 4 ≤ m) (live:m ≤ N) (w:R.family.label 4) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    let A:=R.family.path.rep N p m
    let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
    forced R.makes live w o U*(vacuum R m N p o U:ℂ)=
      alto R.family.path m 4 * ∑' b,q.marked A b (pull 1 o U):=by
  intro A q
  let V:=pull (1:Signed) o U
  have cond : A.eval V=A.eval U:=eval_pull (((R.makes.wilson.represents N p m live).good.labels.moves (1:Signed) o).some) U
  have sure: (A.eval V:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live V).ne'
  have exp:(Real.exp (A.exponent V):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have mul : (A.eval V:ℂ)=(Real.exp (A.exponent V):ℂ)*(A.activities.gas A.p V:ℂ):=Complex.ofReal_mul _ _
  have gas:(A.activities.gas A.p V:ℂ)≠0:=(mul_ne_zero_iff.mp (mul ▸ sure)).2
  have reg:=WilsonInvariantActionRegisteredTranslate.original R.makes live w o U
  have full:field R.makes live w o U=alto R.family.path m 4*q.density 0 (R.family.localSection 4) A V/(A.eval V:ℂ):=by
    have move:=anchor R age live w o U
    change field R.makes live w o U=(alto R.family.path m 4/(A.eval U:ℂ))*q.density 0 (R.family.localSection 4) A V at move
    rw [←cond] at move
    exact move.trans (by ring)
  have diff:=eq_sub_of_add_eq' (separated R.makes live w o U).symm
  rw [full,reg] at diff
  rw [diff]
  change (alto R.family.path m 4*q.density 0 (R.family.localSection 4) A V/(A.eval V:ℂ)-
    alto R.family.path m 4*q.exponentialEntry 0 (R.family.localSection 4) A V)*(A.activities.gas A.p V:ℂ)=
    alto R.family.path m 4*∑' b,q.marked A b V
  rw [Coefficient.density,mul]
  field_simp [exp,gas]; ring

theorem numerator (age:R.family.ref 4 ≤ m) (live:m ≤ N) (w:R.family.label 4)
    (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    ‖forced R.makes live w o U‖*vacuum R m N p o U ≤ weight R m N p o U *
      (safety R.family m * stock R.family m * ((R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m N p w)):=by
  let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
  have income:=entryOk 4 N p m R.makes age live ((R.family.factory 4 N p).terminal.symm w)
  have sale:=WilsonReportRootedPartners.physical (R:=R) live q income.1 income.2 (pull 1 o U)
  have amt:(R.family.labels.level 4).coeffSize q.x = Next.UVStress.quota R.family 4 m N p w:=rfl
  change ‖_‖≤ if _=∅ then 0 else _*_*((stock R.family m)*(R.family.labels.level 4).coeffSize q.x) at sale
  rw [amt] at sale
  have cost:‖∑' b,q.marked (R.family.path.rep N p m) b (pull 1 o U)‖ ≤
      weight R m N p o U*safety R.family m*(stock R.family m*Next.UVStress.quota R.family 4 m N p w):=by
    dsimp only [weight]
    split_ifs at sale ⊢ <;> simpa only [zero_mul] using sale
  have same:=congrArg norm (billed R age live w o U)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (solvent R live o U).le,norm_mul] at same
  have eng:‖alto R.family.path m 4‖=(R.family.S.a m^4)⁻¹:=by
    simp [alto,Complex.norm_real,Real.norm_of_nonneg (R.family.S.a_pos m).le]
  rw [same,eng]
  exact (mul_le_mul_of_nonneg_left cost (inv_nonneg.mpr (pow_nonneg (R.family.S.a_pos m).le _))).trans_eq (by ring)

theorem on_run (age:R.family.ref 4 ≤ m) (live:m ≤ N) (w:R.family.label 4) (budget:ℝ)
    (paid:Next.UVStress.quota R.family 4 m N p w ≤ R.family.S.a m^4*budget)
    (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    ‖forced R.makes live w o U‖ ≤
      (weight R m N p o U/vacuum R m N p o U) * (safety R.family m*stock R.family m*budget):=by
  have nonneg:0≤weight R m N p o U:=by dsimp only [weight];split <;> positivity
  have ca:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos m) _
  have cash:(R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m N p w≤budget:=by
    have h:=mul_le_mul_of_nonneg_left paid (inv_pos.mpr ca).le; rwa [←mul_assoc,inv_mul_cancel₀ ca.ne',one_mul] at h
  have g:=solvent R live o U
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ g).mpr
  apply (numerator R age live w o U).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cash (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (stage R.family m).columns_ge))) nonneg

end YM.Integration.WilsonMatrixOriginalGermForeground
