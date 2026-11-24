import YM.Integration.WilsonReportHarvestUpperLabel

/-! The same finite mark calibrated on the measured frame can enter the
original marked spine at the spatial admission date. The two dates may
occur in either order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReadmittedSource
open Function Filter Lattice Wilson RG Source Extra.Histories Extraction Spec RG12 RG17
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Harvest
open WilsonReportHarvestSourceReach
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{order:Extraction.Order}{table:Table C.book}{F:Final C order table}

def filed (L:Layout F)(d:ℕ)(r:ℝ)(w:C.label d)(U:Emblems C d)(m N per:ℕ):Palette C d :=
  Many.point U (chunk (WilsonReportingUnitOrbit.primary d)
    ((C.factory d N per).terminal.symm (atRef L d r (N,per) w))) N m

theorem carried (L:Layout F)(d:ℕ)(r:ℝ)(w:C.label d)(U:Emblems C d)(m N per:ℕ)(live:m ≤ N):
    Many.point U (filed L d r w U m N per) m N =
      chunk (WilsonReportingUnitOrbit.primary d) ((C.factory d N per).terminal.symm (atRef L d r (N,per) w)) := by
  rw [Many.weave_fine live,filed,Many.point,dif_neg (Nat.not_lt.mpr live),LinearEquiv.apply_symm_apply]

theorem original (L:Layout F):
    ∀ᶠ m:ℕ in atTop,∀b d N per:ℕ,∀rail:Rail C,∀B:ℕ→ℕ→ℝ,
      ∀V:Sight C d per,∀U:Emblems C d,Spine rail B F.room.cutoff b per d N V U →
      ∀r:ℝ,∀w:C.label d,C.ref d ≤ L.level r → L.level r ≤ N → b ≤ m → m ≤ N →
      size (filed L d r w U m N per) ≤
        (C.S.a m/C.S.a N)^(d+2)*(C.S.a (L.level r)/C.S.a m)*
          mass C d ((C.S.a (L.level r):ℂ)^d • L.shift d r w) := by
  filter_upwards [string_paid (C:=C) (show 0 < (1:ℝ) by norm_num)] with m budget
  intro b d N per rail B V U spine r w aged alive begun live
  let q:=C.S.a m/C.S.a N
  let h:=C.S.a (L.level r)/C.S.a m
  let x:=(C.S.a (L.level r):ℂ)^d • L.shift d r w
  let y:=(C.factory d N per).terminal.symm (atRef L d r (N,per) w)
  have bought:=WilsonReportingUpperChartPrice.bare (per:=per) F.room.cutoff aged alive x
  change mass C d (WilsonReportingFactorySingleton.upper F.room.cutoff d (L.level r) N per x) ≤
    C.S.a (L.level r)/C.S.a N*mass C d x at bought
  have same:=WilsonReportingRegulatedFactory.upper L ((C.S.a (L.level r):ℂ)^d) d r w N per
  rw [div_self (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')),one_smul] at same
  rw [same] at bought
  have paid:=Spine.downsized F.room.cutoff spine begun live le_rfl (chunk (WilsonReportingUnitOrbit.primary d) y)
  change size ((finer U live).symm (chunk (WilsonReportingUnitOrbit.primary d) y)) ≤
    advanceCost C d live*size (chunk (WilsonReportingUnitOrbit.primary d) y) at paid
  rw [size_chunk] at paid
  have price:stringCost C live ≤ q:=by
    simpa only [one_mul,←mesh,elapsed,q] using budget N live
  have q0:0 ≤ q:=(div_pos (C.S.a_pos _) (C.S.a_pos _)).le
  have eq:C.S.a (L.level r)/C.S.a N=q*h:=by
    dsimp only [q,h];field_simp [(C.S.a_pos m).ne',(C.S.a_pos N).ne']
  rw [eq] at bought
  change size (Many.point U (chunk (WilsonReportingUnitOrbit.primary d) y) N m) ≤ _
  rw [Many.point,dif_neg (Nat.not_lt.mpr live)]
  calc _ ≤ advanceCost C d live*mass C d y:=paid
       _ ≤ (q*q^d)*((q*h)*mass C d x):=mul_le_mul
            (mul_le_mul_of_nonneg_right price (pow_nonneg q0 d)) bought (mass_nonneg ..) (mul_nonneg q0 (pow_nonneg q0 _))
       _ = _:=by change _=q^(d+2)*h*mass C d x;rw [pow_succ q (d+1),pow_succ q d];ring

end YM.Integration.WilsonReportHarvestReadmittedSource
