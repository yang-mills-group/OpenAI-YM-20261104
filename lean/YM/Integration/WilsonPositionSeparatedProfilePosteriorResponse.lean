import YM.Integration.WilsonPositionSeparatedProfilePosteriorWave

/-! The actual nonbare increment over the original positive one-block Wilson
calculation. Both normalized measures use the same coarse configuration and
forest. The old action remains inside a single signed centered integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfilePosteriorResponse
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction WilsonCoherentForestMeasure
open WilsonLocalHeldKernelChart WilsonLocalCompactPosteriorWeight
open private kernel_env kernel_floor from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {m N per:ℕ}
local notation "op" => R.family.path.levels.clock.op m per
local notation "β" => R.family.path.β N per (m+1)
local notation "coarse" => Config G (R.family.side m per)
local notation "fine" => Config G (R.family.side (m+1) per)

def seed (T:Forest (op).ratio) (V:coarse) (u:T.Slice G) := (op).density β (T.drape u) V*bare β (T.drape u)

def bareRead (V:coarse) (H:fine→ℝ):ℝ :=
  (op).push β (fun U=>bare β U*H U) V/(op).push β (bare β) V

private theorem base (live:m+1≤N) (T:Forest (op).ratio) (V:coarse) {H:fine→ℝ}
    (env:Envelope H) (gi:GaugeInvariant H) :
    Integrable (fun u=>seed R (N:=N) T V u*H (T.drape u)) (T.order G) ∧
    (∫u,seed R (N:=N) T V u*H (T.drape u) ∂T.order G)=(op).push β (fun U=>bare β U*H U) V := by
  let C:fine→ℝ:=fun U=>(op).density β U V*bare β U*H U
  have bare0:Envelope (bare β:fine→ℝ):=⟨(bare_cont β).measurable,(isCompact_univ.exists_bound_of_continuousOn (bare_cont β).continuousOn).imp fun _ a U=>a U (mem_univ U)⟩
  have ce:Envelope C:=((kernel_env (op) β (R.family.path.levels.blocks m per).branches V).mul bare0).mul env
  have pg:Pinned op C:=by
    intro a pins U
    have d:=projected R N per m (fun ℓ=>ℓ V) a pins U
    have dp:=Multi.AxisShift.chosen_positive R.makes.wilson ((Nat.le_succ m).trans live) V
    change (op).density β (Lattice.gauge a U) V/(R.family.path.rep N per m).eval V=(op).density β U V/(R.family.path.rep N per m).eval V at d
    have same: (op).density β (Lattice.gauge a U) V=(op).density β U V:=(div_left_inj' dp.ne').mp d
    dsimp only [C];rw [same,bare_gauge β U a,gi a U]
  letI:IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  have pre:Envelope (fun u:T.Slice G=>C (T.drape u)):=⟨ce.meas.comp T.continuous_drape.measurable,ce.cost.imp fun _ bound u=>bound (T.drape u)⟩
  refine ⟨pre.integrable _,(T.pack C (ce.integrable _) pg).symm.trans ?_⟩
  apply integral_congr_ae;filter_upwards with U;change _*_*_= _*(_*_);ring

theorem normalizer (live:m+1≤N) (T:Forest (op).ratio) (V:coarse) :
    Integrable (seed R (N:=N) T V) (T.order G) ∧ 0<(∫u,seed R (N:=N) T V u ∂T.order G) ∧
    (∫u,seed R (N:=N) T V u ∂T.order G)=(op).push β (bare β) V := by
  have held:=base R live T V (H:=fun _=>1) (Envelope.const _) (fun _ _=>rfl)
  simp only [mul_one] at held
  refine ⟨held.1,?_,held.2⟩
  obtain ⟨c,cp,lower⟩:=kernel_floor R N per m live
  have pos (u:T.Slice G):0<seed R (N:=N) T V u:=mul_pos (cp.trans_le (lower _ _)) (bare_pos β _)
  apply (integral_pos_iff_support_of_nonneg (fun u=>(pos u).le) held.1).mpr
  have su:Function.support (seed R (N:=N) T V)=univ:=Set.eq_univ_of_forall fun u=>(pos u).ne'
  letI:IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  simp [su]

private theorem covariance {Ω:Type} [MeasurableSpace Ω] (μ:Measure Ω) (a b h:Ω→ℝ)
    (ia:Integrable a μ) (ib:Integrable b μ) (ih:Integrable (fun u=>a u*h u) μ)
    (ij:Integrable (fun u=>b u*h u) μ) (ap:0<(∫u,a u ∂μ)) (bp:0<(∫u,b u ∂μ)) :
    let A:=∫u,a u ∂μ
    let B:=∫u,b u ∂μ
    let m:=(∫u,b u*h u ∂μ)/B
    let x:=fun u=>(a u-A/B*b u)*(h u-m)
    Integrable x μ ∧ (∫u,a u*h u ∂μ)/A-m=(∫u,x u ∂μ)/A := by
  intro A B m x
  let w:=fun u=>a u-A/B*b u
  let v:=fun u=>a u*h u-A/B*(b u*h u)
  have wi:Integrable w μ:=ia.sub (ib.const_mul _)
  have vi:Integrable v μ:=ih.sub (ij.const_mul _)
  have formed:x=fun u=>v u-w u*m:=by funext u;dsimp only [x,v,w];ring
  have zero:(∫u,w u ∂μ)=0:=by
    dsimp only [w];rw [integral_sub ia (ib.const_mul _),integral_const_mul];change A-A/B*B=0;rw [div_mul_cancel₀ _ bp.ne',sub_self]
  rw [formed]
  refine ⟨vi.sub (wi.mul_const _),?_⟩
  rw [integral_sub vi (wi.mul_const _),integral_mul_const,zero,zero_mul,sub_zero]
  dsimp only [v];rw [integral_sub ih (ij.const_mul _),integral_const_mul]
  have nA:A≠0:=ap.ne'
  have nB:B≠0:=bp.ne'
  dsimp only [m];field_simp [nA,nB]

variable {I:Type} [Fintype I]

def response (live:m+1<N) (grade:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (op).ratio) (V:coarse) (H:fine→ℝ) (u:T.Slice G) :=
  let a:=amount R live grade T (incident R T d o) V
  let b:=seed R (N:=N) T V
  (a u-((∫v,a v ∂T.order G)/(∫v,b v ∂T.order G))*b u)*(H (T.drape u)-bareRead R (N:=N) V H)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (d:I→ℕ) (grade:ℕ) (ord:5≤grade) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      let μ:=T.order G
      let B:=incident R T d o
      let Z:=∫u,amount R live grade T B V u ∂μ
      let X:=response R live grade d o T V H
      Integrable X μ ∧ 0<Z ∧ WilsonPositionSeparatedProfilePosteriorWave.read R live grade d o T V H-
        bareRead R (N:=N) V H=(∫u,X u ∂μ)/Z := by
  filter_upwards [WilsonLocalCompactPosterior.original R simple marks fees slow d 0 grade ord zero_lt_one]
    with m offer N live per o T V H env gi
  intro μ B Z X
  have real:=offer N live per o T V H env gi
  have c0:=normalizer R live.le T V
  have c1:=base R live.le T V env gi
  have obs:=(covariance μ (amount R live grade T B V) (seed R (N:=N) T V) (fun u=>H (T.drape u)) real.1 c0.1 real.2.1 c1.1 real.2.2.1 c0.2.1)
  have same:(∫u,seed R (N:=N) T V u*H (T.drape u) ∂μ)/(∫u,seed R (N:=N) T V u ∂μ)=bareRead R (N:=N) V H:=by rw [c1.2,c0.2.2];rfl
  dsimp only at obs;rw [same] at obs
  exact ⟨obs.1,real.2.2.1,obs.2⟩

end YM.Integration.WilsonPositionSeparatedProfilePosteriorResponse
