import YM.Integration.WilsonPositionSeparatedProfileCenteredHistory
import YM.Integration.WilsonPositionSeparatedProfileFlatReadout
import YM.Integration.WilsonSeparatedOriginalReplicaRegularity

/-! Every independently computed physical readout of the complete marked
roster recovers the actual older conditional of the same joint profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredReadout
open Function Set MeasureTheory Finset Lattice Wilson RG Source Labels ProjectorNext.Equivariance
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open RG05Readout.Harvest RG05Readout.Many RG05Readout.Records PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage RG05Readout.Velvet
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {v n m N p u:ℕ}

def enrolled (s:Fin v→ℕ) (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) (x:(i:Fin v)→Palette R.family (s i)) (m N p:ℕ) (i:Fin v):=
  Many.point (Y (s i) (N,p)) (x i) m N

/-- The raw palette output is carried back through the exact fitted zero
matrix. No election of a different upper or lower field is made. -/
theorem raw (s:Fin v→ℕ) (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) (x:(i:Fin v)→Palette R.family (s i)) (r:ℝ) (Ψ:Wave (Fin v)) {cap:ℝ}
    (rp:0<r) (enclosed:∀z∈tsupport Ψ.val,∀i,‖z i‖≤cap) (room:r*cap+2*R.family.S.a u<R.family.S.radius p)
    {M:Palette R.family 0} (heard:hears Ψ s x Y n m u 0 N p r M):
    ∃ (top : n+1 ≤ N) (lower : u ≤ n) (length : u ≤ m),
      val ((finer (Y 0 (N,p)) length).symm M) (Suede.mother R.family)=
        dyes R.family u N p (lower.trans (n.le_succ.trans top)) (constellation s (enrolled R s Y x m N p) r Ψ (lower.trans (n.le_succ.trans top)) m (Native.line Suede.pip)) 1/liftVac R.family.path N p u 1:=by
  have well (k:ℕ) (live:k≤N):timely (constellation (C:=R.family) (p:=p) s (enrolled R s Y x m N p) r Ψ live m):=
    fun g=>WilsonSeparatedOriginalReplicaRegularity.physical s (enrolled R s Y x m N p) live Ψ r m g
  obtain ⟨top,report⟩:=heard
  obtain ⟨tape,actual,raw,fee,printed⟩:=report.storied
  refine ⟨top,report.boundary,report.boundary.trans report.h,?_⟩
  rw [show rebases R.family n m 0=1 from pow_zero _,Complex.ofReal_one,inv_one,one_smul] at printed
  have one:=WilsonPositionSeparatedProfileFlatField.read R.makes printed
  rw [actual] at one
  let V:=R.family.path.rep N p u
  have flags:RG.flags V.p.threshold (1:Config G (R.family.side u p))=∅:=(offFlags _ V.p.threshold_pos).self_of_nhds
  rw [← WilsonPositionSeparatedProfileCenteredHistory.held R s (enrolled R s Y x m N p) r Ψ top rp enclosed m well report.boundary room]
  apply (eq_div_iff (noFlagEval (R:=V) flags)).mpr
  exact (mul_comm ..).trans one.symm

private theorem rewind (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) {budget:ℕ→ℕ→ℝ} {start:ℕ→ℕ}
    (rows:Chalice.Anchored R.doors budget R.makes start Y) (first:start 0≤u) (duration : u ≤ m) (live:m≤N) (M:Palette R.family 0):
    (finer (Y 0 (N,p)) duration).symm M=M:=by
  obtain ⟨_,spine⟩:=rows.paid (N,p) 0 ((first.trans duration).trans live)
  have placed:∀j:ℕ,u≤j→j<N→Y 0 (N,p) j (Suede.firstC R.family)=Suede.firstC R.family:=
    (Suede.measured_eq R.makes spine (rows.age 0) first (duration.trans live)).2
  have stationary {j:ℕ} (hj:u≤j) (late:j≤N):(finer (Y 0 (N,p)) hj).symm (Suede.firstC R.family)=Suede.firstC R.family:=by
    induction j,hj using Nat.le_induction with
    | base=>rw [base_value];rfl
    | succ i hi ih=>
      rw [finer_next hi]
      change (finer (Y 0 (N,p)) hi).symm (Y 0 (N,p) i (Suede.firstC R.family))=_
      rw [placed _ hi (by omega),ih (by omega)]
  calc (finer (Y 0 (N,p)) duration).symm M=(finer (Y 0 (N,p)) duration).symm (val M (Suede.mother R.family) • Suede.firstC R.family):=congrArg _ (Suede.letter_sum M).symm
    _=val M (Suede.mother R.family) • Suede.firstC R.family:=by rw [map_smul,stationary duration live]
    _=M:=Suede.letter_sum M

/-- The actual phase-independent number read at a fixed earlier date on the
complete genuine upper field. -/
def value (s:Fin v→ℕ) (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) (x:(i:Fin v)→Palette R.family (s i)) (r:ℝ) (Ψ:Wave (Fin v)) (u m N p:ℕ):ℂ:=
  if date:u≤N then dyes R.family u N p date (constellation s (enrolled R s Y x m N p) r Ψ date m (Native.line Suede.pip)) 1/liftVac R.family.path N p u 1 else 0

/-- Every independent fitted report gives exactly the same true signed
earlier conditional. The reporting chart is the original anchored one. -/
theorem original (s:Fin v→ℕ) (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) {budget:ℕ→ℕ→ℝ} {start:ℕ→ℕ}
    (rows:Chalice.Anchored R.doors budget R.makes start Y) (x:(i:Fin v)→Palette R.family (s i)) (r:ℝ) (Ψ:Wave (Fin v)) {cap:ℝ}
    (rp:0<r) (enclosed:∀z∈tsupport Ψ.val,∀i,‖z i‖≤cap) (room:r*cap+2*R.family.S.a u<R.family.S.radius p)
    (first:start 0≤u) (live:m≤N) {M:Palette R.family 0} (heard:hears Ψ s x Y n m u 0 N p r M):
    val M (Suede.mother R.family)=value R s Y x r Ψ u m N p:=by
  obtain ⟨top,lower,duration,actual⟩:=raw R s Y x r Ψ rp enclosed room heard
  rw [rewind R Y rows first duration live M] at actual
  rwa [value,dif_pos (lower.trans (n.le_succ.trans top))]

end YM.Integration.WilsonPositionSeparatedProfileCenteredReadout
