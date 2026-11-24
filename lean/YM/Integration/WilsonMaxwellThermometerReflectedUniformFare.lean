import YM.Integration.WilsonMaxwellThermometerReflectedCovariance
import YM.Integration.WilsonPositionCorrectedCap
/-! The full two-chirality measurement at every small real radius of the
actual position frame. The original cutoff and period are chosen last. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedUniformFare
open Function Filter Set Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider Source Source.Drops
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open RG17 PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionCapTransport (Book)
open WilsonPositionThermometerCapStation (Group)
open WilsonPositionCorrectedCap (adjusted)
open WilsonMaxwellThermometerReflectedPhysicalColumns (height levels tag active)
open WilsonMaxwellThermometerReflectedStation (Name source phase)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{T:Table R.family.book}
variable (F:Final R.family f T)(P:ℝ→tower T)(V:Store G)
variable {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}(A:ℝ→Group R.family 6)
variable (a:Axis)(b:Sec G 6)(d:Fin 2→ℕ)(fit:∀i,levels i<d i)

theorem original (simple:G.Simple)(book:Book (f:=f) (l:=l) (H:=H) A P)(lead:Leading F P)
    (e:ℕ)(η:ℝ)(positive:0<η):
    ∃C:ℝ,0 ≤ C ∧ ∀ᶠ r in trail,let Z:=adjusted F P V A r
      ∀N p:ℕ,Z.station.k<N → ∀(s:Name)(i:Fin 2),
      fee (source R d fit Z a b Z.station.k s N p) e i ≤ C*(R.family.path.levels.clock.hatBeta Z.station.k)^η:=by
  let I:=Name×Fin 2
  let h (j:I):Fin 7:=height j.2
  let v(j:I):(Bel R.family.book).Field (h j):=
    (fields R.family.labels (h j)).symm (tag a b j.1.1 j.1.2.2 j.2)
  have seat(m:ℕ):=WilsonPositionCorrectedCap.mixed F P V A book lead h v m
  have dates:Tendsto (fun r=>(adjusted F P V A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun m=>(seat m).mono fun _ paid=>paid.1
  let wage(j:I):ℝ:=
    let D:=R.family.labels.level (h j)
    (Fintype.card (Alma D)*(e+1:ℕ):ℕ)*(‖phase j.1 j.2‖*((2:ℝ)^(univ.sup fun w:D.Index=>(D.grades w).2)*
      (WilsonPositionThermometerStationNorm.cost R.family (h j)*(‖v j‖+costHint 0))))
  let C:ℝ:=∑j:I,‖wage j‖
  refine ⟨C,sum_nonneg fun _ _=>norm_nonneg _,?_⟩
  filter_upwards [seat 0,dates.eventually (WilsonMaxwellThermometerReflectedPhysicalColumns.original
      (f:=f) (H:=H) R simple η positive e d fit),
    dates.eventually ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0)] with r filing all pos
  intro Z N p after s i
  let j:I:=(s,i)
  let D:=R.family.labels.level (levels i)
  let c:ℝ:=(Fintype.card (Alma D)*(e+1:ℕ):ℕ)
  let L:ℝ:=(2:ℝ)^(univ.sup fun w:D.Index=>(D.grades w).2)
  let o:ℝ:=WilsonPositionThermometerStationNorm.cost R.family (levels i)
  let β:=R.family.path.levels.clock.hatBeta Z.station.k
  let hi:=filing.2.2.2.2.2 j
  have normbound:‖active R Z a b s.1 s.2.2 i‖ ≤ ‖v j‖+costHint 0:=by
    change ‖Z.change (h j) (v j)‖ ≤ _
    calc
      _=‖(Z.change (h j) (v j)-v j)+v j‖:=by rw [sub_add_cancel]
      _≤‖Z.change (h j) (v j)-v j‖+‖v j‖:=norm_add_le ..
      _≤_:=by linarith only [hi]
  have nonneg:0≤β^η:=Real.rpow_nonneg pos _
  have oh:0≤o:=by unfold o WilsonPositionThermometerStationNorm.cost;positivity
  have raw:=all Z rfl filing.2.1 N p after a b s.1 s.2.2 (phase s) i
  apply raw.trans
  change c*(‖phase s i‖*(L*β^η*(o*‖active R Z a b s.1 s.2.2 i‖))) ≤ C*β^η
  calc
    _≤c*(‖phase s i‖*(L*β^η*(o*(‖v j‖+costHint 0)))):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by dsimp [L]; positivity) nonneg)
      exact mul_le_mul_of_nonneg_left normbound oh
    _=wage j*β^η:=by change c*(‖phase s i‖*(L*β^η*(o*(‖v j‖+costHint 0))))=
        (c*(‖phase s i‖*(L*(o*(‖v j‖+costHint 0)))))*β^η;ring
    _≤C*β^η:=mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (single_le_sum (f:=fun j:I=>‖wage j‖) (fun _ _=>norm_nonneg _) (mem_univ j))) nonneg
end YM.Integration.WilsonMaxwellThermometerReflectedUniformFare
