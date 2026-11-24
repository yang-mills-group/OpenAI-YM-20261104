import YM.Integration.WilsonMasterReportingWords
import YM.Next.WARD_BIN.Hats
import YM.MergeProof.North.Sultan

/-! The finite reporting chart on any original label, with its engineering
power, genuine entry cost, and actual threshold-to-coupling change. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMasterCoordinatePrice
open Function Filter Lattice Wilson RG OPE MergeProof MergeProof.Ribbons MergeProof.Accent
open Extra.Histories Pert.Asymptotics RG16 RG16.Literal Trace.Physical.GermGraph
open Source Overlay Bid ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Next.Rank WilsonMasterReportingWords
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G}

theorem threshold (H : C.Makes) {N p m : ℕ} (hm : m ≤ N) :
    regulatorRun C N p m / (C.path.rep N p m).p.threshold ≤ 2 := by
  have law := (H.wilson.represents N p m hm)
  rw [law.vac]
  apply (div_le_iff₀ (C.path.levels.budget m).threshold_pos).2
  have b := WardBin.hot C.path.levels m
  have a := Overlay.beta_positive H.wilson (N:=N) (p:=p) hm
  have hs := Real.sqrt_pos.mpr a
  have hs' := Real.sqrt_pos.mpr b
  have hrel : Real.sqrt (C.path.levels.clock.hatBeta m) ≤ 2*Real.sqrt (C.path.β N p m) := by
    nlinarith only [Real.sq_sqrt b.le,Real.sq_sqrt a.le,law.band.1,hs.le,hs'.le]
  have g : regulatorRun C N p m ≤ 2*C.path.levels.clock.hatCoupling m := by
    change (Real.sqrt (C.path.β N p m))⁻¹ ≤ 2*(Real.sqrt (C.path.levels.clock.hatBeta m))⁻¹
    rw [← one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hs hs').2 (by simpa only [one_mul] using hrel)
  exact g.trans (mul_le_mul_of_nonneg_left (WardBin.stepGle C.path.levels m) zero_le_two)

theorem positive_grade (H : C.Makes) (N p d m : ℕ) (hm : m ≤ N) (y : C.label d) :
    (C.labels.level d).coeffSize (gMap C N p d m y) ≤
      (2:ℝ)^(degree (C.labels.level d))*(C.labels.level d).coeffSize y := by
  let c := regulatorRun C N p m / (C.path.rep N p m).p.threshold
  have hc : 0 < c := div_pos (g_pos H hm) (C.path.rep N p m).p.threshold_pos
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [gMap,Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg hc.le _)]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ hc.le (threshold H hm) _).trans
    (pow_le_pow_right₀ one_le_two (Finset.le_sup (f:=fun i => ((C.labels.level d).grades i).2) hi)))
    (norm_nonneg _)

theorem paid (H : C.Makes) (N p d m : ℕ) (op : Opened C d m p) (hm : m ≤ N)
    (y : C.label d) :
    (C.labels.level d).coeffSize (coordinates H N p d m op hm y) ≤
      (2:ℝ)^(degree (C.labels.level d))*2*Spindle.paid C d m N p y := by
  let z := (C.factory d N p).terminal.symm y
  let K := (2:ℝ)^(degree (C.labels.level d))
  have purchased := positive_grade H N p d m hm (alto C.path m d • fitting d N p m H op hm z)
  change _ ≤ K*_ at purchased
  rw [Size.smul] at purchased
  have fit := (size_gap d N p m H op hm z).1
  change (C.labels.level d).coeffSize (fitting d N p m H op hm z) ≤
    2*Next.UVStress.quota C d m N p y at fit
  have cancel : ‖alto C.path m d‖*(C.S.a m)^d = 1 := by
    rw [alto,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos m).le,
      inv_mul_cancel₀ (pow_pos (C.S.a_pos m) d).ne']
  calc
    _ ≤ K*(‖alto C.path m d‖*(2*Next.UVStress.quota C d m N p y)) :=
      purchased.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fit (norm_nonneg _))
        (pow_nonneg zero_le_two _))
    _ = _ := by
      rw [← Log.obey_quota]
      change K*(_*(2*(_*_))) = K*2*_
      linear_combination (K*2*Spindle.paid C d m N p y)*cancel

theorem linear_scale (H : C.Makes) (N p d m : ℕ) (op : Opened C d m p) (hm : m ≤ N)
    (a : ℂ) (y : C.label d) :
    coordinates H N p d m op hm (a • y) = a • coordinates H N p d m op hm y := by
  unfold coordinates dress gMap
  simp only [map_smul]
  exact smul_comm _ _ _

/-- One unit raw-label quote controls the entire finite vector, with the
positive additive padding at the original grade carried explicitly. -/
theorem scaled (H : C.Makes) (N p d m : ℕ) (op : Opened C d m p) (hm : m < N)
    (y : C.label d) :
    (C.labels.level d).coeffSize (coordinates H N p d m op hm.le y) ≤
      (((2:ℝ)^(degree (C.labels.level d))*2)*fly C.path.levels d m / plumR C d 1 m)*
        ((C.labels.level d).coeffSize y + (C.S.a m)^d) := by
  let a := (C.labels.level d).coeffSize y + (C.S.a m)^d
  have ha : 0 < a := add_pos_of_nonneg_of_pos (Work.G08.size_nonneg _ _) (pow_pos (C.S.a_pos _) _)
  let z := ((a:ℂ)⁻¹) • y
  have hz : (C.labels.level d).coeffSize z ≤ 1 := by
    change (C.labels.level d).coeffSize (((a:ℂ)⁻¹) • y) ≤ 1
    rw [Size.smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg ha.le,← div_eq_inv_mul]
    exact (div_le_one ha).2 (le_add_of_nonneg_right (pow_nonneg (C.S.a_pos _).le _))
  have unit := paid_new C N p m d H z 1 one_pos hz op.post hm
  have hp := stockpit C m d 1 one_pos
  have hval : Spindle.paid C d m N p z ≤ fly C.path.levels d m / plumR C d 1 m :=
    (le_div_iff₀ hp).2 ((mul_comm _ _).le.trans unit)
  have he : y = (a:ℂ) • z := by
    unfold z; rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'),one_smul]
  calc
    _ = a*(C.labels.level d).coeffSize (coordinates H N p d m op hm.le z) := by
      conv_lhs => rw [he,linear_scale,Size.smul,Complex.norm_real,Real.norm_of_nonneg ha.le]
    _ ≤ a*(((2:ℝ)^(degree (C.labels.level d))*2)*(fly C.path.levels d m / plumR C d 1 m)) :=
      mul_le_mul_of_nonneg_left ((paid H N p d m op hm.le z).trans
        (mul_le_mul_of_nonneg_left hval (by positivity))) ha.le
    _ = _ := by change a*(_*(_/_)) = (_*_/_)*a; ring

end YM.Integration.WilsonMasterCoordinatePrice

