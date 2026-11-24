import YM.RGComparison01.Sensor.Test
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge}

section pack
variable {c f:Side} {S:StepData c f} {D W r H β σ C Λ:ℝ} {k j:ℕ} (T : Tube G S) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
    (X:Before G σ C S.patch.J S.kernel (k+3))
local notation "P" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Ps" => (X.tables T.high S.patch)
variable (hE : X.Service F T.high T.up ρ)
variable (hq:Larger (G:=G) S) (hv:T.up.Bounds T.high σ C Λ)
variable (hb : (Fintype.card (Joint F G):ℝ)≤D) (hD : 1 ≤ D)
local notation "sT" => Before.Service.trailCost Ps (k+3)
local notation "u" => fun w:ℝ=> tally Ps D w X.Z k G
include hE hq hv hb hD T X
lemma till (a:Pressure.Cell f)(hr : r ≤ (X.tables T.high S.patch).horizon) (ht:r≤1) (he : Before.Service.trailCost Ps (k+3)*r+r*W ≤ 1) : Purchase (testF F ρ a) k r W 1 (u W) := by
    have hP: 0 ≤ u W:= by unfold tally sight; positivity
    refine ⟨hP,fun x hx=> ⟨Measurable.indicator (ready F ρ a x) measurableSet_closedBall,fun z=> ?_⟩⟩
    by_cases h:z∈closedBall 0 W
    · have hw:=mem_closedBall_zero_iff.mp h; rw [mem_ball_zero_iff] at hx; exact (charm T F ρ X hE hq hv hb hD x a z (height T F ρ X hE hq hv _ _ hx hr ht hw he) (hx.le.trans ht) (((norm_snd_le x).trans_lt hx).trans_le hr) hw).shimmy (Eventually.of_forall fun _=> indicator_of_mem h _)
    exact Brush.zi (Eventually.of_forall fun y=> indicator_of_notMem h _) hP zero_le_one

omit hE hq hv hb hD T X
lemma fare_nn (V:ChartPrices)(D W Z:ℝ)(k:ℕ)(G:Gauge) :0 ≤ tally V D W Z k G:=by unfold tally sight; positivity
lemma covers (x y A L : ℝ) (i:ℕ)(hx:0≤x) (hy:0 ≤ y) (hA:0 ≤ A) (hL:0≤L) : A*(1+(1+|L+x+1|)*1)^i ≤ A*(1+(1+|L+y+1|)*1)^i*(1+x)^i:=by
    rw [mul_assoc,← mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) hA
    · positivity
    rw [abs_of_nonneg (by positivity : 0 ≤ L+x+1),abs_of_nonneg (by positivity : 0 ≤ L+y+1)]; nlinarith only [hx,hy,hL,mul_nonneg hy hx,mul_nonneg hL hx]
include hE hq hv T X
omit hq hv
lemma aerial (z:Y) : fusion F ρ z 0 = 0:= by
   unfold fusion; simp only [Prod.snd_zero,Lapis.zeroO F T.up T.high ρ σ C X hE,Prod.fst_zero,zero_smul,add_zero] -- check arity includes p b σ
   rfl
lemma ghost0 (a:Pressure.Cell f) (z:Y) : testF F ρ a z 0 = 0:=by
    rw [native,aerial T F ρ X hE z,map_zero, (fine_supply F X.labels|>.1),WilsonStartup.face_one,G.price_one] -- maybe hQ omitted
lemma ally (a:Pressure.Cell f) (z:Y): FlatAt 2 (testF F ρ a z) 0:= by
    have hh: IsLocalMin (testF F ρ a z) 0 := Eventually.of_forall fun i=> by rw [ghost0 T F ρ X hE a z]; exact (G.price_range _).1
    have hx := hh.fderiv_eq_zero
    intro i hi; interval_cases i
    · exact norm_eq_zero.mp (by rw [norm_iteratedFDeriv_zero,ghost0 T F ρ X hE a z,norm_zero])
    apply norm_eq_zero.mp; rw [norm_iteratedFDeriv_one,hx,norm_zero]
include hb hD hq hv
lemma portal (a:Pressure.Cell f)(hr : r ≤ (X.tables T.high S.patch).horizon) (ht:r≤1) (he : Before.Service.trailCost Ps (k+3)*r+r*W ≤ 1) (hp:0≤W) : Probe (testF F ρ a) k k 2 r W (u W) (u W):=by
    have hv₀:=hE.x_pos; have hv':‖(0:P)‖< (Ps).horizon:=by rwa [norm_zero]
    refine ⟨⟨fun C h=>?_⟩, till T F ρ X hE hq hv hb hD a hr ht he,fun z=> ?_,fun z=> ally T F ρ X hE a z⟩
    · let M:= sT; have hu₀ : 0<M:= hE.trail_lipschitz hv hq rfl rfl |>.1; let z:= min (M+C)⁻¹ (min 1 (Ps).horizon)
      have hz: 0<z:= lt_min (inv_pos.mpr (add_pos_of_pos_of_nonneg hu₀ h)) (lt_min zero_lt_one hv₀)
      have hC: sT*z+z*C ≤ 1:=by change M*z+z*C ≤ 1; rw [mul_comm z C,← add_mul]; exact (mul_le_mul_of_nonneg_left (min_le_left ..) (add_pos_of_pos_of_nonneg hu₀ h).le).trans (mul_inv_cancel₀ (add_pos_of_pos_of_nonneg hu₀ h).ne'|>.le)
      have hh:= till T F ρ X hE hq hv hb hD a ((min_le_right ..).trans (min_le_right ..)) ((min_le_right ..).trans (min_le_left ..)) hC
      exact ⟨u C,Eventually.mono (ball_mem_nhds 0 hz) (fun i hi=> hh.toll i hi)⟩
    have hZ:= charm T F ρ X hE hq hv hb hD 0 a z (by rw [aerial T F ρ X hE z,map_zero,norm_zero]; norm_num) (by rw [norm_zero]; norm_num) hv' (le_refl _)
    refine hZ.climb ?_ le_rfl; unfold tally glare; exact covers _ _ _ _ k (norm_nonneg _) hp (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (Lapis.luminous F (Classical.arbitrary _) T.up T.high ρ σ C Λ X hq hv hE D hD hb 0 (mem_ball_zero_iff.mpr hv') |>.nonneg) -- check
end pack
end YM.RGComparison01.Sensor
