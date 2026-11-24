import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Physical
import YM.Integration.WilsonPositionHomogeneousLeading
import YM.Integration.WilsonMSDictionaryVector

/-! The actual homogeneous name carried through the bounded original position
change before applying the physical zero-horizon comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Frame
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FVA2 FVA2.Register FVA2.Scale Maxwell XSpace XSpace.Normalize
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonNestedReportedCharacterCurrentBayQ198Physical (coefficient)
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)

def archive (r:ℝ)(d:ℕ):Free R.family d≃ₗ[ℂ]Free R.family d:=
  (homogeneous F J Z r d).trans (J r d).symm

theorem name (r:ℝ)(d:ℕ)(v:Free R.family d):J r d (archive F J Z r d v)=homogeneous F J Z r d v:=by
  exact (J r d).apply_symm_apply _

theorem converges (simple:G.Simple)(lead:Leading F J){A:(Bel R.family.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in Trace.Pilot.trail,Frame.obedient F A (J r) d)(d:ℕ)(v:Free R.family d):
    Tendsto (fun r=>archive F J Z r d v) RG17.home (𝓝 v):=by
  have limits:=WilsonPositionHomogeneousLeading.field F J Z lead paid simple d v
  apply limits.congr
  intro r
  simp [archive,homogeneous,WilsonPositionPrescribedFrame.positioned,WilsonPositionPrescribedLift.field]

theorem bounded (simple:G.Simple)(lead:Leading F J){A:(Bel R.family.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in Trace.Pilot.trail,Frame.obedient F A (J r) d)(d:ℕ):
    ∃C:ℝ,0≤C ∧ ∀ᶠr in RG17.home,∀v:Free R.family d,‖archive F J Z r d v‖≤C*‖v‖:=by
  let B:=WilsonMSDictionaryVector.basis R.family d
  let rate:=fun i=>‖(B.coord i).toContinuousLinearMap‖*(‖B i‖+1)
  refine ⟨∑i,rate i,Finset.sum_nonneg fun i _=>mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (by positivity),?_⟩
  have head:∀ᶠr in RG17.home,∀i,‖archive F J Z r d (B i)‖≤‖B i‖+1:=Filter.eventually_all.mpr fun i=>
    ((converges F J Z simple lead paid d (B i)).norm.eventually_lt_const (lt_add_one _)).mono fun _ h=>h.le
  filter_upwards [head] with r budget v
  calc
    ‖archive F J Z r d v‖=‖∑i,(B.repr v i) • archive F J Z r d (B i)‖:=by
      simp_rw [←map_smul]
      rw [←map_sum,B.sum_repr]
    _≤∑i,‖(B.repr v i) • archive F J Z r d (B i)‖:=norm_sum_le ..
    _≤∑i,rate i*‖v‖:=by
      apply sum_le_sum
      intro i _
      rw [norm_smul]
      have hi:‖B.repr v i‖≤‖(B.coord i).toContinuousLinearMap‖*‖v‖:=(B.coord i).toContinuousLinearMap.le_opNorm v
      exact (mul_le_mul hi (budget i) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [rate];ring)
    _=(∑i,rate i)*‖v‖:=(sum_mul ..).symm

theorem original {T:Campaign R}(simple:G.Simple)(W:Campaign.Pillars R T){b:ℝ}
    (source:FundedOriginalProperties.{u} simple b W)(pace:WilsonWindowReportingPace.Slow R.kit){B:ℕ}(bp:0<B)
    (fac:OPE.Facilities R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (lead:Leading F J){A:(Bel R.family.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in Trace.Pilot.trail,Frame.obedient F A (J r) d){n:ℕ}(d:Caps n){K:Set (Points n)}
    (compact:IsCompact K)(safe:K⊆conf n){θ:ℝ→ℝ}(heat:Trace.Pilot.Coupling G θ)(q:ℕ)
    {σ:ℝ}(sp:0<σ):
    ∀ε:ℝ,0 < ε→∀ᶠr in RG17.home,∀x∈K,∀viewer:Viewers F,∀v:(i:Fin n)→Free R.family (d i),
      ‖PhysMS.measured F viewer (homogeneous F J Z r) v r x-
        coefficient F Q (RG17.posed r x) (fun i=>homogeneous F J Z r (d i) (v i)) 0‖≤
        ε*(θ r)^q*r^(4-σ)*(∏i,‖v i‖):=by
  choose A₀ pos costs using fun i:Fin n=>bounded F J Z simple lead paid (d i)
  let cap:=∏i,A₀ i
  have ca:0≤cap:=prod_nonneg fun i _=>pos i
  intro ε ep
  have large:0<cap+1:=by linarith
  have budget:=WilsonNestedReportedCharacterCurrentBayQ198Physical.original F Q simple W source pace bp fac J lead paid d
    compact safe heat q sp (div_pos ep large)
  filter_upwards [budget,Filter.eventually_all.mpr costs,heat.positive,RG17.positiveLength] with r held limits hp rp x hx viewer v
  let a:=fun i=>archive F J Z r (d i) (v i)
  have before:=held x hx viewer a
  dsimp only at before
  simp only [a,name] at before
  have named:Orbits.moment (spectator F viewer) (RG17.posed r x) (fun i=>homogeneous F J Z r (d i) (v i))=
      PhysMS.measured F viewer (homogeneous F J Z r) v r x:=by
    change Orbits.moment (spectator F viewer) (r • x).ofLp _=_
    rw [Orbits.observed,named_fin (spectator F viewer) (spectate F viewer).laws.toSymmetric _ (Work.A05.smul_conf rp (safe hx))]
    rfl
  rw [named] at before
  apply before.trans
  have dvd:(∏i,‖a i‖)≤cap*∏i,‖v i‖:=by
    dsimp [cap]
    rw [←prod_mul_distrib]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>limits i (v i))
  have product:0≤(∏i,‖v i‖):=prod_nonneg fun _ _=>norm_nonneg _
  have hot:0≤(θ r)^q:=pow_nonneg hp.le _
  have space:0≤r^(4-σ):=Real.rpow_nonneg rp.le _
  calc
    _ ≤ ε/(cap+1)*(θ r)^q*r^(4-σ)*(cap*(∏i,‖v i‖)):=mul_le_mul_of_nonneg_left dvd (by positivity)
    _ ≤ ε*(θ r)^q*r^(4-σ)*(∏i,‖v i‖):=by
      have capFee:ε/(cap+1)*cap≤ε:=by
        calc
          _ ≤ ε/(cap+1)*(cap+1):=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
          _=ε:=div_mul_cancel₀ _ (ne_of_gt large)
      calc
        _=(ε/(cap+1)*cap)*((θ r)^q*r^(4-σ)*(∏i,‖v i‖)):=by ring
        _≤ε*((θ r)^q*r^(4-σ)*(∏i,‖v i‖)):=mul_le_mul_of_nonneg_right capFee (by positivity)
        _=_:=by ring

end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Frame
end
