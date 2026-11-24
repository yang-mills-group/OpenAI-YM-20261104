import YM.Integration.WilsonOriginalPublicPivotFaces

/-! The filed Wilson section on its own inversion tree. Each occupied slot is
divided by its native angular order before it is combined with the other slots. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedLetters
open Function Finset PowerSeries Lattice Wilson RG Labels XSpace
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2 Precision
open scoped Classical BigOperators ContDiff
variable {G : Gauge} (R : Run G) (p : Period) (T : p.Tree)
local notation "F" d:max => R.family.labels.level d

def source (d : ℕ) (o : Cover) (b : (F d).Index) (u : T.Field G) : ℂ :=
  (R.family.localSection d).places (Pi.single b 1) (wrap p.side o) (T.links u)

theorem grade (d : ℕ) (o : Cover) (b : (F d).Index) :
    Comparison.RG02.Assembly.GradeAt ((F d).grades b).2 (source R p T d o b) := by
  let L := (T.logdir (G:=G)).toContinuousLinearMap
  have ranked := Comparison.RG02.Bare.Signals.primary (C:=R.family) b
    (YM.FVAAlt2.Block.clothes R d) (wrap p.side o)
  have eq : source R p T d o b =
      ((R.family.localSection d).places (Pi.single b 1) (wrap p.side o) ∘
        represent (G:=G) (n:=p.side)) ∘ L := by
    funext u
    exact congrArg ((R.family.localSection d).places (Pi.single b 1) (wrap p.side o)) (T.represent_eq u).symm
  rw [eq]
  exact ranked.coarse L.contDiff.contDiffAt L.map_zero

def letter (d : ℕ) (o : Cover) (b : (F d).Index) : Bare.Series T G :=
  PowerSeries.mk fun q => coeff (q+((F d).grades b).2)
    (Taylor.expandTaylor (T.basis G) (source R p T d o b))

theorem shifted (d : ℕ) (o : Cover) (b : (F d).Index) :
    PowerSeries.X^((F d).grades b).2 * letter R p T d o b =
      Taylor.expandTaylor (T.basis G) (source R p T d o b) := by
  ext k : 1
  rw [coeff_X_pow_mul']
  split_ifs with le
  · rw [letter,coeff_mk,Nat.sub_add_cancel le]
  · apply Taylor.from_real (T.basis G)
    intro u
    rw [map_zero,Taylor.expandTaylor,coeff_mk,Taylor.divided_eval,
      (grade R p T d o b).vanish k (Nat.lt_of_not_ge le)]
    simp

variable {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ) (z : I → Cover)

omit [Fintype I] [LinearOrder I] in
private theorem product (axes : (i:I) → (R.family.labels.level (d i)).Index) (s : Finset I) :
    Taylor.expandTaylor (T.basis G) (∏i∈s,source R p T (d i) (z i) (axes i)) =
      ∏i∈s,Taylor.expandTaylor (T.basis G) (source R p T (d i) (z i) (axes i)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change Taylor.expandTaylor (T.basis G) (fun _ => (1:ℂ)) = 1
    simpa using Taylor.expand_const (T.basis G) (1:ℂ)
  | @insert i s fresh ih =>
    simp only [Finset.prod_insert fresh]
    have hs : ContDiffAt ℝ ω (∏j∈s,source R p T (d j) (z j) (axes j)) 0 := by
      rw [show (∏j∈s,source R p T (d j) (z j) (axes j)) =
        (fun u => ∏j∈s,source R p T (d j) (z j) (axes j) u) from funext fun u=>Finset.prod_apply u s _]
      exact contDiffAt_prod (fun j _ => (grade R p T (d j) (z j) (axes j)).smooth)
    rw [Taylor.expand_mul _ (grade R p T (d i) (z i) (axes i)).smooth hs,ih]

theorem original (axes : (i:I) → (R.family.labels.level (d i)).Index) :
    WilsonThermometerPositionTunedSlope.finite R d p z T axes =
      Bare.normalized T G (∏i,letter R p T (d i) (z i) (axes i)) := by
  have placed : Complex.ofRealCLM ∘ (WilsonPositionProgramCopyTop.planted R p d z axes ∘ T.links) =
      ∏i,source R p T (d i) (z i) (axes i) := by
    funext u
    change (Complex.ofReal ∘ Kick.topMark (Lodge.basisR R) univ d axes p.side z) (T.links u) = _
    simpa only [Finset.prod_apply,source] using
      congrFun (Boot.combined R univ d axes z p.side) (T.links u)
  have full : Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
      (WilsonPositionProgramCopyTop.planted R p d z axes ∘ T.links)) =
      PowerSeries.X^(Kick.depthF univ d axes) * ∏i,letter R p T (d i) (z i) (axes i) := by
    rw [placed,product,Kick.depthF,← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => (shifted R p T _ _ _).symm)
  have normed : WilsonPositionProgramCopyTop.normalized R p d z axes T =
      PowerSeries.X^(Kick.depthF univ d axes) * Bare.normalized T G (∏i,letter R p T (d i) (z i) (axes i)) := by
    rw [WilsonPositionProgramCopyTop.normalized,full,←Bare.normalized_scalar T,Bare.scalar,map_pow,PowerSeries.map_X]
  ext q : 1
  rw [WilsonThermometerPositionTunedSlope.finite,coeff_mk,normed,coeff_X_pow_mul]

end YM.Integration.WilsonOriginalPublicPlantedLetters
