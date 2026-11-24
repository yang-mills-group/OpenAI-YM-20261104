import YM.Integration.WilsonRegisteredAffineLedger
import YM.Integration.WilsonRegisteredAffineHalo

/-! The Taylor polynomial and the original signed sum of every short row,
centered at the authentic compact forest background on the genuine
registered physical angular event. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineSource
open Filter Set Finset Lattice Wilson Tree RG Source OPE.Therm Precision PertExtension PhysicalNext.Repeat.Legato
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots Pert.Asymptotics
open WilsonInheritedRegisteredField WilsonReportingForestAngularFare WilsonRegisteredAffineTaylor
open scoped Classical
variable {G:Gauge}

def width (R:Run G) (N per k:ℕ) :=
  (regulatorRun R.family N per k*((Real.log (R.family.path.levels.clock.hatBeta k))^2/32)) /
    (R.family.path.rep N per k).p.threshold

theorem original (R:Run G) (simple:G.Simple) :
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) (d:ℕ) (_hr:R.family.ref d ≤ m+1)
      (w:R.family.label d) (o:Site (R.family.side (m+1) per)) (b H q:ℕ)
      (T:Forest ((R.family.path.levels.clock.op m per).ratio)) (B:Finset T.Free)
      (v:({i:T.Free|i∉moving T B}:Set T.Free)→G.El) (X:↥(moving T B)→G.Color),
    let k:=m+1
    let Z:=packet R.makes live w o
    let A:=R.family.path.rep N per k
    let L:=R.family.labels.level d
    let β:=R.family.path.levels.clock.hatBeta k
    let g:=regulatorRun R.family N per k
    let u (t:ℝ):=restored T B v (Chart.expLinks G (↥(moving T B)) (t • X))
    let r:=width R N per k
    b*(4*A.p.B+2)+2*A.p.B ≤ H → ‖X‖ ≤ g*(Real.log β^2/32) → q+1 ≤ A.p.order →
    u 1∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut β) →
    ∃ D:Directions G (R.family.side k per),A.p.dirBound o D ∧ (∀z:ℝ,increment (u 0) (z • D)=u (z/r)) ∧
      let f:=fun i=>if coverNumber A.p.B (Z.support i)<b then Z.maskedTerm A i (u 1) else 0
      let p:=fun i=>if coverNumber A.p.B (Z.support i)<b then jet (Z.regular i) (u 0) D q r else 0
      Summable f ∧ Summable p ∧ ‖(∑' i,f i)-(∑' i,p i)‖ ≤
        (R.family.path.levels.params k).columns*L.coeffSize (L.core Z.x)*(r^(q+1)/q.factorial) := by
  filter_upwards [WilsonRegisteredAffineRows.original R simple] with m charge
  intro N per live d hr w o b H q T B v X k Z A L β g u r range size order cold
  obtain ⟨a,bounded,ray⟩:=WilsonRegisteredAffineDirection.located T B v X
  have bp:1<β:=(R.family.path.levels.fits.delayed k)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans bp)).trans_le
    (R.makes.wilson.represents N per k live).band.1))
  have rp:0<r:=div_pos (mul_pos gp (div_pos (sq_pos_of_pos (Real.log_pos bp)) (by norm_num))) A.p.threshold_pos
  let D:=r⁻¹ • a
  have dir:A.p.dirBound o D:=by
    intro e
    calc
      ‖D e‖ = r⁻¹*‖a e‖:=by change ‖r⁻¹ • a e‖=_;rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr rp.le)]
      _ ≤ r⁻¹*(g*(Real.log β^2/32)):=mul_le_mul_of_nonneg_left ((bounded e).trans size) (inv_nonneg.mpr rp.le)
      _ = A.p.threshold:=by
        have found:r*A.p.threshold=g*(Real.log β^2/32):=div_mul_cancel₀ _ A.p.threshold_pos.ne'
        rw [←found,←mul_assoc,inv_mul_cancel₀ rp.ne',one_mul]
      _ ≤ _:=le_mul_of_one_le_right A.p.threshold_pos.le (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have located (z:ℝ):increment (u 0) (z • D)=u (z/r):=by
    have go:=ray (z/r) 0
    change u (z/r+0)=increment (u 0) ((z/r) • a) at go
    rw [add_zero] at go
    simpa only [D,smul_smul,div_eq_mul_inv] using go.symm
  have safe:=charge N per live d hr w o b H T B v X range size cold
  have study (z:ℝ) (hz:z∈Set.Icc 0 r) (i:ℕ) (cut:coverNumber A.p.B (Z.support i)<b):
      Healthy A.p.threshold (Z.support i) (increment (u 0) (z • D)) :=
    (congrArg (Healthy A.p.threshold (Z.support i)) (located z)).mpr
      ((safe (z/r) ⟨div_nonneg hz.1 rp.le,(div_le_one rp).mpr hz.2⟩).2 i cut)
  have table:=WilsonRegisteredAffineLedger.original (C:=R.family) (k:=k) (N:=N) (per:=per) (d:=d)
    R.makes live hr w o b q (u 0) D rp dir order study
  refine ⟨D,dir,located,?_⟩
  have finish:increment (u 0) (r • D)=u 1:=by rw [located,div_self rp.ne']
  dsimp only at table
  rw [finish] at table
  exact table

end YM.Integration.WilsonRegisteredAffineSource
end
