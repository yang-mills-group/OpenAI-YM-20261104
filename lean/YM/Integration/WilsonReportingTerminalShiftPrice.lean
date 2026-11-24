import YM.Integration.WilsonReportingCellTaylorRemainder
import YM.Integration.WilsonReportingTopEnvelope
import YM.Integration.ActualNormalizedPush
import YM.RG17.Gathers

/-! Joint translation of the genuine finite-cutoff reporting primaries at the
last Wilson block. Its Taylor remainder pays the complete engineering powers
of the cutoff. All lower test jets are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalShiftPrice
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Spec RG12 RG17
open RG05Readout Address Native Pulse Extra.Multi.BasisCost WilsonReportingCellTaylorRemainder
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {T:YM.Table C.book} {F:Final C f T}
  (L:Layout F) {I:Type*} [Fintype I] (d:I→ℕ) (w:(i:I)→C.label (d i))

def roster (r:ℝ) (N per:ℕ) (o:I→Site (C.side N per)) (U:Config G (C.side N per)):ℂ:=
  ∏ i,C.O N per (atRef L (d i) r (N,per) (w i)) (o i) U

def ranks (C:Family G) (d:I→ℕ):ℕ:= ∑i,slots (C.labels.level (d i))

def budget (r:ℝ):ℝ:=
  ∏i,price (C.localSection (d i))*mass C (d i) (L.shift (d i) r (w i))

def fare (r A:ℝ) (t k:ℕ):ℝ:=
  A*(C.S.a (L.level r)*(C.S.block t).val/r)^(k+1)*
    (C.path.levels.clock.hatBeta (t+1))^(ranks C d)*budget L d w r

def error (φ:Wave I) (r:ℝ) (t per k:ℕ) (y:Cloud I) (child:I→Bud C per t)
    (o:I→Site (C.side (t+1) per)) (U:Config G (C.side (t+1) per)) : ℂ:=
  let v:Cloud I:=fun i=>displacement C per t (child i)
  let step:=C.S.a t/r
  (φ.val (y+step • v)-jet φ k y v step)*roster L d w r (t+1) per o U

private theorem priced (r:ℝ) (N per:ℕ) (aged:∀i,C.ref (d i)≤L.level r)
    (live:L.level r≤N) (o:I→Site (C.side N per)) (U:Config G (C.side N per)) :
    ‖roster L d w r N per o U‖≤(C.S.a (L.level r)/C.S.a N)^(∑i,(d i+1))*
      (C.path.levels.clock.hatBeta N)^(ranks C d)*budget L d w r := by
  let a:=C.S.a (L.level r)/C.S.a N
  let β:=C.path.levels.clock.hatBeta N
  have paid (i:I):‖C.O N per (atRef L (d i) r (N,per) (w i)) (o i) U‖≤
      a^(d i+1) * β^slots (C.labels.level (d i)) *
          (price (C.localSection (d i))*mass C (d i) (L.shift (d i) r (w i))) := by
    have h:=WilsonReportingTopEnvelope.field F.room.cutoff (aged i) live (L.shift (d i) r (w i)) (o i) U
    rw [atRef,(C.linearO N per (d i) (o i)).map_smul,Pi.smul_apply,smul_eq_mul,Complex.ofReal_pow]
    change _ ≤ a^(d i+1)*β^_*(_*_)
    linarith only [h,show price (C.localSection (d i))*a^(d i+1)*β^slots (C.labels.level (d i))*mass C (d i) (L.shift (d i) r (w i))
      =a^(d i+1)*β^slots (C.labels.level (d i))*(price (C.localSection (d i))*mass C (d i) (L.shift (d i) r (w i))) from by ring]
  unfold roster
  rw [norm_prod]
  calc
    _ ≤ ∏i, (a^(d i+1)*β^slots (C.labels.level (d i))*(price (C.localSection (d i))*mass C (d i) (L.shift (d i) r (w i)))) :=
      prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>paid i)
    _ = _ := by rw [prod_mul_distrib,prod_mul_distrib,prod_pow_eq_pow_sum,prod_pow_eq_pow_sum];rfl

theorem original (φ:Wave I) (K:Set (Cloud I)) (compact:IsCompact K)
    (k:ℕ) (order:k+1=∑i,(d i+1)) :
    ∃A:ℝ,0≤A ∧ ∀r:ℝ,0<r → (∀i,C.ref (d i)≤L.level r) →
      ∀t:ℕ,L.level r≤t+1 → C.S.a t≤r → ∀per:ℕ,∀y∈K,∀child:I→Bud C per t,
      ∀o:I→Site (C.side (t+1) per),∀U:Config G (C.side (t+1) per),
        ‖error L d w φ r t per k y child o U‖≤fare L d w r A t k := by
  obtain ⟨A,hA,quote⟩:=WilsonReportingCellTaylorRemainder.original φ K compact k
  refine ⟨A,hA,?_⟩
  intro r rp ages t live small per y hy child o U
  let v:Cloud I:=fun i=>displacement C per t (child i)
  have belongs (i:I):v i∈Native.box:=by
    simpa only [v,smul_zero,add_zero] using dist_box C per t (child i) Native.box0
  have high := quote y hy v belongs (C.S.a t/r) (div_pos (C.S.a_pos _) rp) ((div_le_one rp).2 small)
  have stock:=priced L d w r (t+1) per ages live o U
  rw [←order] at stock
  change ‖(φ.val (y+(C.S.a t/r) • v)-jet φ k y v (C.S.a t/r))*_‖≤_
  rw [norm_mul]
  calc
    _ ≤ (A*(C.S.a t/r)^(k+1))*((C.S.a (L.level r)/C.S.a (t+1))^(k+1)*
      (C.path.levels.clock.hatBeta (t+1))^(ranks C d)*budget L d w r) :=
      mul_le_mul high stock (norm_nonneg _) (mul_nonneg hA (pow_nonneg (div_pos (C.S.a_pos _) rp).le _))
    _ = _ := by
      have step:(C.S.a t/r)*(C.S.a (L.level r)/C.S.a (t+1))=
          C.S.a (L.level r)*(C.S.block t).val/r:=by
        rw [Schedule.a_step]
        field_simp [(C.S.a_pos _).ne',rp.ne']
      unfold fare
      rw [←step,mul_pow]
      ring

end YM.Integration.WilsonReportingTerminalShiftPrice
