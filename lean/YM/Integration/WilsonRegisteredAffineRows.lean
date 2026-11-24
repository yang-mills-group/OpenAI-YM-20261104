import YM.Integration.WilsonRegisteredAffineForest
import YM.Integration.WilsonReportingForestAngularFare
import YM.IterationFour.Running

/-! The genuine compact relative angular room stays in the original
regular domain along the whole segment for every retained source row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineRows
open Filter Lattice Wilson Tree RG OPE.Therm Precision PertExtension PhysicalNext.Repeat.Legato
open Push.AbsoluteSums.Animals WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonRegisteredAffineForest WilsonInheritedRegisteredField WilsonReportingForestAngularFare
open scoped Classical
variable {G:Gauge}

private theorem global_bonds (G:Gauge) : ∃ C:ℝ,0<C ∧
    ∀ {c f:Side} {S:StepData c f} (T:Forest S.ratio) (B:Finset T.Free)
      (v:({i:T.Free|i∉moving T B}:Set T.Free)→G.El) (X:↥(moving T B)→G.Color)
      {t:ℝ},t∈Set.Icc 0 1→∀e:Edge (Site f),
    let u (a:ℝ):=restored T B v (Chart.expLinks G (↥(moving T B)) (a • X))
    G.chord (u t e*(u 1 e)⁻¹)  ≤  2*C*‖X‖ := by
  obtain ⟨A,r,ap,rp,room⟩:=bonds G
  refine ⟨max A r⁻¹,ap.trans_le (le_max_left ..),?_⟩
  intro c f S T B v X t time e u
  by_cases small:‖X‖ ≤ r
  · exact (room T B v X small time e).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left ..) (by norm_num)) (norm_nonneg _))
  calc
    _  ≤  2:=G.chord_le_two _
    _ = 2*r⁻¹*r:=by rw [mul_assoc,inv_mul_cancel₀ rp.ne',mul_one]
    _  ≤  2*max A r⁻¹*‖X‖:=mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right ..) (by norm_num))
      (le_of_not_ge small) rp.le (by positivity)

private theorem threshold (R:Run G) (simple:G.Simple) {C:ℝ} (cp:0<C) :
    ∀ᶠ k:ℕ in atTop,∀ N per (_hk:k ≤ N),
    let β:=R.family.path.levels.clock.hatBeta k
    let g:=Pert.Asymptotics.regulatorRun R.family N per k
    angularCut β+8*C*(g*(Real.log β^2/32))  ≤  (R.family.path.rep N per k).p.threshold := by
  let A:=R.family.path.levels
  have grows:=Next.Rank.Station.hat_rate A simple
  have logs:=Real.tendsto_log_atTop.comp grows
  filter_upwards [logs.eventually_ge_atTop (2+C), (Real.tendsto_log_atTop.comp logs).eventually_ge_atTop (3:ℝ)] with k sc yc
  intro N per hk β g
  let s:=Real.log β
  let y:=Real.log s
  let gh:=A.clock.hatCoupling k
  have js : 2+C ≤ s:=sc
  have jy : 3 ≤ y:=yc
  have s1:1 ≤ s:=by linarith only [js,cp]
  have sp:0<s:=zero_lt_one.trans_le s1
  have gp:0 ≤ gh:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have actual:g ≤ 2*gh:=(IterationFour.Currency.hat_g R.makes N per k hk).2
  have mon : s^3  ≤  A.clock.monitor k := by
    change s^3 ≤ Real.exp (y^2)
    rw [←Real.exp_log sp,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change (3:ℝ)*y ≤ y^2
    nlinarith only [mul_nonneg (show 0 ≤ y by linarith only [jy]) (sub_nonneg.mpr jy)]
  have twice : Real.sqrt (Real.sqrt s)  ≤  s := by
    have first:Real.sqrt s ≤ s:=by nlinarith only [Real.sq_sqrt sp.le,Real.sqrt_nonneg s,s1,sq_nonneg (Real.sqrt s-1)]
    have next:1 ≤ Real.sqrt s:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt s1
    have second:Real.sqrt (Real.sqrt s) ≤ Real.sqrt s:=by
      nlinarith only [Real.sq_sqrt (Real.sqrt_nonneg s),Real.sqrt_nonneg (Real.sqrt s),next,sq_nonneg (Real.sqrt (Real.sqrt s)-1)]
    exact second.trans first
  have ex : angularCut β  ≤  gh*s^2 :=
    (mul_le_mul_of_nonneg_left twice (mul_nonneg gp sp.le)).trans_eq (by ring)
  have delta:8*C*(g*(s^2/32))  ≤  gh*((C/2)*s^2):=by
    calc
      _  ≤  8*C*((2*gh)*(s^2/32)):= by gcongr
      _ = _:=by ring
  have all : (1+C/2)*s^2 ≤ s^3:=
    (mul_le_mul_of_nonneg_right (show 1+C/2 ≤ s by linarith only [js,cp]) (sq_nonneg _)).trans_eq (by ring)
  have same: (R.family.path.rep N per k).p=A.budget k := (R.makes.wilson.represents N per k hk).vac
  rw [same]
  change _  ≤  gh*A.clock.monitor k
  calc
    _  ≤  gh*s^2+gh*((C/2)*s^2):=add_le_add ex delta
    _ = gh*((1+C/2)*s^2):=by ring
    _  ≤  _:=mul_le_mul_of_nonneg_left (all.trans mon) gp

/-- The input is an actual angular rejection test on the links around the
true site. The conclusion concerns the same frozen relative interpolation
and every genuine column in the submitted retained field at once. -/
theorem original (R:Run G) (simple:G.Simple) :
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) (d:ℕ) (_hr:R.family.ref d  ≤  m+1)
      (w:R.family.label d) (o:Site (R.family.side (m+1) per)) (b H:ℕ)
      (T:Forest ((R.family.path.levels.clock.op m per).ratio)) (B:Finset T.Free)
      (v:({i:T.Free|i∉moving T B}:Set T.Free)→G.El) (X:↥(moving T B)→G.Color),
    let k:=m+1
    let Z:=packet R.makes live w o
    let A:=R.family.path.rep N per k
    let β:=R.family.path.levels.clock.hatBeta k
    let g:=Pert.Asymptotics.regulatorRun R.family N per k
    let u (t:ℝ):=restored T B v (Chart.expLinks G (↥(moving T B)) (t • X))
    b*(4*A.p.B+2)+2*A.p.B ≤ H→‖X‖ ≤ g*(Real.log β^2/32)→
    u 1∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut β)→
    ∀ t∈Set.Icc (0:ℝ) 1,Healthy A.p.threshold (neighbors (H+H) o) (u t) ∧
      ∀ i,coverNumber A.p.B (Z.support i)<b→Healthy A.p.threshold (Z.support i) (u t) := by
  obtain ⟨C,cp,rails⟩:=global_bonds G
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (threshold R simple cp)] with m billed
  intro N per live d hr w o b H T B v X k Z A β g u placed radius accepted t time
  have move (z:Face (Per (R.family.side k per))):G.chord (faceValue (u t) z) ≤ 
      G.chord (faceValue (u 1) z)+4*(2*C*‖X‖):=
    plaquette (u 1) (u t) (rails T B v X time) z
  have safe : u t∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) A.p.threshold:=by
    intro z hz
    calc
      _  ≤  _:=move z
      _ ≤ angularCut β+8*C*(g*(Real.log β^2/32)):=by
        apply add_le_add (accepted z hz)
        calc
          _ = 8*C*‖X‖:=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_left radius (by positivity)
      _  ≤  _:=billed N per live
  have halo:=WilsonPhysicalHistoryKioskPlaquettes.healthy H o (u t) safe
  refine ⟨halo,fun i price=>Finset.disjoint_of_subset_left (fun x seen=>?_) halo⟩
  apply (neighbors_mem _ _ _).mpr
  exact ((WilsonRegisteredShortField.belongs R.makes live hr w o b i x price seen).trans placed).trans (by omega)

end YM.Integration.WilsonRegisteredAffineRows
end
