import YM.Integration.WilsonRegisteredMeasurableJet
import YM.Integration.WilsonRegisteredAffineSource
import YM.Integration.WilsonCoherentForestReadout

/-! The signed previous registered angular polynomial is a Borel observable
of the *same* saved forest coordinates as the original held conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredFrozenReading
open Filter Set Finset Function MeasureTheory Lattice Wilson Tree RG Source OPE.Therm Precision PertExtension PhysicalNext.Repeat.Legato
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots Pert.Asymptotics
open WilsonReportingForestAngularFare WilsonInheritedRegisteredField WilsonRegisteredAffineSource WilsonCoherentForestMeasure
open WilsonCoherentReportingForest WilsonCoherentForestReadout
open scoped Classical
variable {G:Gauge} (R:Run G) {m N per d:ℕ} (live:m<N) (w:R.family.label d)
  (o:Site (R.family.side (m+1) per)) (b q:ℕ)
  (T:Forest ((R.family.path.levels.clock.op m per).ratio)) (B:Finset T.Free) (η:ℂ→L[ℝ]ℝ)
section definitions
local notation "k" => (m+1)
local notation "Z" => packet R.makes live w o
local notation "A" => R.family.path.rep N per k
local notation "E" => moving T B

def previous (U:Config G (R.family.side k per)) : ℂ :=
  ∑' i,if coverNumber (A).p.B ((Z).support i)<b then (Z).maskedTerm A i U else 0

def reading (z:Sample T B G):ℝ :=
  ∑' i,if coverNumber (A).p.B ((Z).support i)<b then
    WilsonRegisteredMeasurableJet.printed η ((Z).regular i) (restored T B z.1 1)
      ((width R N per k)⁻¹ • drift T B z.2) q (width R N per k) else 0

theorem measured (hr:R.family.ref d ≤ k) : Measurable (reading R live w o b q T B η) := by
  have prior:=WilsonTranslatedFactory.based R.makes hr live o ((R.family.factory d N per).terminal.symm w)
  have form:(Z).Format o R.family.params (A):=prior.1
  have pivot:Measurable (fun z:Sample T B G=>restored T B z.1 1):=
    restored_meas T B (fun z:Sample T B G=>z.1) (fun _=>1) measurable_fst measurable_const
  have direction:Measurable (fun z:Sample T B G=>(width R N per k)⁻¹ • drift T B z.2):=
    (measurable_drift (G:=G) T B).const_smul ((width R N per k)⁻¹:ℝ)
  unfold reading
  apply Measurable.tsum
  intro i
  by_cases cut:coverNumber (A).p.B ((Z).support i)<b
  · simp only [cut,if_true]
    exact WilsonRegisteredMeasurableJet.measured η ((Z).regular i) (form.smooth i).borel _ pivot _ direction q _
  · simp only [cut,if_false];exact measurable_const

end definitions

private theorem project_series {n:Side} (p:BudgetPoint) (Y:ℕ→Support n)
    (F:ℕ → Config G n→ℂ) (η:ℂ→L[ℝ]ℝ) (W:Config G n) (D:Directions G n) (r:ℝ) (b q:ℕ)
    (form:∀i,p.Regular (Y i) (F i)) (clean:∀i,coverNumber p.B (Y i)<b→Healthy p.threshold (Y i) W)
    (order:q≤p.order)
    (sum:Summable (fun i=>if coverNumber p.B (Y i)<b then WilsonRegisteredAffineTaylor.jet (F i) W D q r else 0)):
    (∑' i,if coverNumber p.B (Y i)<b then WilsonRegisteredMeasurableJet.printed η (F i) W D q r else 0)=
      η (∑' i,if coverNumber p.B (Y i)<b then WilsonRegisteredAffineTaylor.jet (F i) W D q r else 0) := by
  refine Eq.trans ?_ (ContinuousLinearMap.map_tsum η sum).symm
  apply tsum_congr
  intro i
  by_cases cut:coverNumber p.B (Y i)<b
  · simp only [cut,if_true]
    exact WilsonRegisteredMeasurableJet.original η W D q r (form i) (clean i cut) order
  · simp [cut]

theorem original (simple:G.Simple) :
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) (d:ℕ) (_hr:R.family.ref d ≤ m+1)
      (w:R.family.label d) (o:Site (R.family.side (m+1) per)) (b H q:ℕ)
      (T:Forest ((R.family.path.levels.clock.op m per).ratio)) (B:Finset T.Free)
      (η:ℂ→L[ℝ]ℝ) (z:Sample T B G),
    let k:=m+1
    let Z:=packet R.makes live w o
    let A:=R.family.path.rep N per k
    let β:=R.family.path.levels.clock.hatBeta k
    let g:=regulatorRun R.family N per k
    let r:=width R N per k
    b*(4*A.p.B+2)+2*A.p.B ≤ H → ‖z.2‖ ≤ g*(Real.log β^2/32) → q+1 ≤ A.p.order →
    state T B z∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut β) →
    |η (previous R live w o b (state T B z)) - reading R live w o b q T B η z| ≤
      ‖η‖*((R.family.path.levels.params k).columns*(R.family.labels.level d).coeffSize
        ((R.family.labels.level d).core Z.x)*(r^(q+1)/q.factorial)) := by
  filter_upwards [WilsonRegisteredAffineRows.original R simple] with m charge
  intro N per live d hr w o b H q T B η z k Z A β g r range size order cold
  let u (t:ℝ):=restored T B z.1 (Chart.expLinks G (↥(moving T B)) (t • z.2))
  let W:=restored T B z.1 (1:↥(moving T B)→G.El)
  let D:=r⁻¹ • drift T B z.2
  have bp:1<β:=R.family.path.levels.fits.delayed k
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans bp)).trans_le
    (R.makes.wilson.represents N per k live).band.1))
  have rp:0<r:=div_pos (mul_pos gp (div_pos (sq_pos_of_pos (Real.log_pos bp)) (by norm_num))) A.p.threshold_pos
  have dir:A.p.dirBound o D:=by
    intro e
    calc
      ‖D e‖ = r⁻¹*‖drift T B z.2 e‖:=by
        change ‖r⁻¹ • drift T B z.2 e‖=_;rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr rp.le)]
      _ ≤ r⁻¹*(g*(Real.log β^2/32)):=mul_le_mul_of_nonneg_left
        ((WilsonCoherentReportingForest.size T B z.2 e).trans size) (inv_nonneg.mpr rp.le)
      _ = A.p.threshold:=by
        have found:r*A.p.threshold=g*(Real.log β^2/32):=div_mul_cancel₀ _ A.p.threshold_pos.ne'
        rw [←found,←mul_assoc,inv_mul_cancel₀ rp.ne',one_mul]
      _ ≤ _:=le_mul_of_one_le_right A.p.threshold_pos.le (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have located (t:ℝ):increment W (t • D)=u (t/r):=by
    funext e
    change G.lieExp (t • (r⁻¹ • drift T B z.2 e)) * W e = _
    dsimp only [u]
    rw [WilsonCoherentReportingForest.edge T B z.1 z.2 (t/r) e,smul_smul,div_eq_mul_inv]
  have finish:u 1=state T B z:=by simp only [u,one_smul];rfl
  have ready:u 1∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut β):=by
    rw [finish];exact cold
  have safe:=charge N per live d hr w o b H T B z.1 z.2 range size ready
  have study (t:ℝ) (ht:t∈Icc (0:ℝ) r) (i:ℕ) (cut:coverNumber A.p.B (Z.support i)<b):
      Healthy A.p.threshold (Z.support i) (increment W (t • D)) :=
    (congrArg (Healthy A.p.threshold (Z.support i)) (located t)).mpr
      ((safe (t/r) ⟨div_nonneg ht.1 rp.le,(div_le_one rp).mpr ht.2⟩).2 i cut)
  have table:=WilsonRegisteredAffineLedger.original (C:=R.family) (k:=k) (N:=N) (per:=per) (d:=d)
    R.makes live hr w o b q W D rp dir order study
  dsimp only at table
  rw [located,div_self rp.ne',finish] at table
  have form:Z.Format o R.family.params A:=
    (WilsonTranslatedFactory.based R.makes hr live o ((R.family.factory d N per).terminal.symm w)).1
  have zero:increment W ((0:ℝ) • D)=W:=by rw [zero_smul,Work.G07.at_zero_increment]
  have clean(i:ℕ)(hi:coverNumber A.p.B (Z.support i)<b):Healthy A.p.threshold (Z.support i) W:=by
    exact (congrArg (Healthy A.p.threshold (Z.support i)) zero).mp (study 0 ⟨le_rfl,rp.le⟩ i hi)
  have read:reading R live w o b q T B η z=η (∑' i,
      if coverNumber A.p.B (Z.support i)<b then WilsonRegisteredAffineTaylor.jet (Z.regular i) W D q r else 0):=
    project_series A.p Z.support Z.regular η W D r b q form.smooth clean (Nat.le_of_succ_le order) table.2.1
  rw [read,←map_sub,←Real.norm_eq_abs]
  exact (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left table.2.2 (norm_nonneg _))

end YM.Integration.WilsonRegisteredFrozenReading
end
