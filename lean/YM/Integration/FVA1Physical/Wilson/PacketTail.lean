import YM.Integration.FVA1Physical.Wilson.PortalPacket
import YM.Integration.FVA1Physical.Sources.Round2.CutBankPrice

/-! Under the unrestricted measured Haar posterior, an incoming distributed
packet sees the copied healthy collar up to any power, at every torus period.
Even on failed fields we control the actual clipped chart polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset Matrix MeasureTheory MvPolynomial Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Wave MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Bakery.Film MSbar.Midpoint MSbar.Measuring Push.Uniform
open YM.Integration.FVA1Physical.Round2.Curvature Progress.DirectedRecipe
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem packet_global_bound (p m:ℕ) :
    ∀ᶠ y:ℝ in atTop,∀ {f:Side} (b:Site f) (s:ℕ) (δ g:ℝ) (T:Nesting G f),
    δ ≤ 1 → BankPaid b y s p m δ T → lensT y g → |g| ≤ 1 →
    ∀ W:Config G f,|clockReading p g T (chartLog g W)| ≤ y^(m+3) := by
  let r:=(LocalH.geom_patch G).choose
  have r0:0 ≤ r:=(LocalH.geom_patch G).choose_spec.1.le
  let C:ℝ:=(p+1:ℕ)*(1+4*r)^(m+1)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop C] with y y1 large
  intro f b s δ g T small bank clock g1 W
  have y0:0 ≤ y:=zero_le_one.trans y1
  have ha:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have invg:= (inverse_clock_le_linear y1 clock).2
  have window:1+|g⁻¹| * r ≤ (1+4*r)*y:=by nlinarith only [mul_le_mul_of_nonneg_right invg r0,y1,mul_nonneg y0 r0]
  have rate:y^δ ≤ y:=by simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le y1 small)
  let Z:=chartLog g W
  have row(i:ℕ)(hi:i≤p):|g^i*eval Z (PowerSeries.coeff i T)| ≤ y*((1+4*r)*y)^(m+1) := by
    have budget:=bank i hi
    have cap:‖Z-0‖ ≤ |g⁻¹| * r:=by rw [sub_zero];exact chartLog_norm_bound ..
    have buy:=Bout.looks ha (Bout.across Z budget.2 ha cap budget.1 0)
    rw [abs_mul,abs_pow]
    apply (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) g1)).trans
    exact buy.trans (mul_le_mul rate (pow_le_pow_left₀ (by positivity) window _)
      (pow_nonneg (by positivity) _) y0)
  unfold clockReading taste picture
  simp only [PowerSeries.coeff_map]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (fun i hi=>row i (Nat.lt_succ_iff.mp (mem_range.mp hi)))).trans
  rw [sum_const,card_range,nsmul_eq_mul]
  calc (p+1:ℕ)*(y*((1+4*r)*y)^(m+1)) = C*y^(m+2):=by simp only [C,mul_pow,pow_succ];ring
       _ ≤ y*y^(m+2):=mul_le_mul_of_nonneg_right large (pow_nonneg y0 _)
       _ = y^(m+3):=by ring

theorem packet_tail_season (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage) (P:Patch)
    (K:KernelChoices) (branch:P.Branches K G) (p m s:ℕ) {D:ℝ} (hD:0 ≤ D) (u:ℝ) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
    Season V H H' x A.pre A.post A.S (courage G P.L x) →
    let y:=tip G P.L x;let g:=A.fClock
    ∀ (Z:Positions (Primary A.c G)) (b:Site A.f),‖g•Z‖ ≤ D*room y →
    let O:=postcard G A.c g Z;let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
    let X:=boxX y b;let Y:=boxY y b;let live:=hotel A.F X Y V O μ (pillow y) (room y)
    let copy:=chambers A.F Y V O μ;let E:=expect A.S A.pre O
    ∀ δ:ℝ,δ≤1 → ∀ T:Nesting G A.f,BankPaid b y s p m δ T →
    let φ:=fun W=>clockReading p g T (chartLog g W)
    |E (live.indicator (φ ∘ copy))-E (φ ∘ canoe (S:=A.S) A.F)| ≤ 2*y^u := by
  let d:ℝ:=(m+3:ℕ)
  obtain ⟨_,chance⟩:=purchased_fluctuation_chance V cle simple H H' P K branch hD (u-d)
  have grow:=Work.E09.betaF_growth G P.L
  have padded:∀ᶠ y:ℝ in atTop,pillow y ≤ room y := by
    filter_upwards [(Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 3,
      eventually_ge_atTop (1:ℝ)] with y lo hi
    have nn:0 ≤ distance y:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _) (Real.log_nonneg hi)
    simpa only [pillow,Cottage.room,Function.comp_apply,mul_comm (3:ℝ) _] using mul_le_mul_of_nonneg_left lo nn
  filter_upwards [chance,grow.eventually (packet_global_bound (G:=G) p m),grow.eventually padded,
      grow.eventually (rendered_packet_collar (G:=G) m s p 1 u),grow.eventually_ge_atTop (8:ℝ)]
    with x rarity price pad exterior large
  intro A patch kernel season y g Z b narrow O μ X Y live copy E δ small T bank φ
  have y1:1 ≤ y:=by dsimp only [y];linarith only [large]
  have y0:0<y:=zero_lt_one.trans_le y1
  have law:=season.case_
  rw [patch] at law
  have clock:lensT y g:=Mosaic.ever y0 law.beta law.upper
  have β:1 ≤ A.pre.beta:=by linarith only [law.beta,large]
  have g0:0 ≤ g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g1:|g| ≤ 1:=by
    rw [abs_of_nonneg g0]
    exact inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt β)
  have bank1:BankPaid b y s p m 1 T:=fun i hi=>⟨(bank i hi).1,Quote.widen (bank i hi).2
    (Real.rpow_le_rpow_of_exponent_le y1 small) le_rfl⟩
  have cap:=price b s δ g T small bank clock g1
  have near:=exterior A.S A.F V cle b O μ pad clock g1 T bank1
  have adm:Admitted O A.pre A.S H'.width H'.paths (ability (tip G A.S.patch.L x)) (lbt (tip G A.S.patch.L x)) 1 :=
    ⟨season.case_.lawful,fun W=>(season.shine W).le,push_strict A.S A.pre.beta season.bends.1 season.shine
    ((A.pre.envelope season.case_.lawful).integrable _) O,A.S.isKernel season.bends.1 _⟩
  have xy:X⊆Y:=halo_subset ..
  have ml:MeasurableSet live:=(garden_main A.F X Y V O μ cle xy).from_here
  have mc:Measurable copy:=(informed A.F X Y V O μ cle xy).1
  have mf:Measurable φ:=(clockReading_continuous ..).measurable.comp (chartLog_meas g)
  let U : Config G A.f → Config G A.f := canoe (S:=A.S) A.F
  let cut:=live.indicator (φ ∘ U)
  have mcanoe:Measurable U:=(canoe_cont A.F).measurable
  have cutbound:Envelope cut:=Envelope.piece ml ⟨mf.comp mcanoe,y^(m+3),fun W=>cap _⟩ (Envelope.const 0)
  have first:|E (live.indicator (φ∘copy))-E cut| ≤ y^u:=by
    apply expect_difference adm ((mf.comp mc).indicator ml) cutbound
    intro W;by_cases hit:W∈live
    · simpa only [cut,Set.indicator_of_mem hit,Function.comp_apply,φ,clockReading] using
        ((abs_sub_comm _ _).le.trans (near W hit))
    simpa only [cut,Set.indicator_of_notMem hit,sub_self,abs_zero] using (Real.rpow_nonneg y0.le u)
  obtain ⟨_,cal,_,_⟩:=rarity A patch kernel season (g•Z) b narrow
  have second:=expect_on_chart O ml adm (φ ∘ U) (mf.comp mcanoe) (pow_nonneg y0.le (m+3))
    (fun W=>cap _) cal.sails
  have tail:y^(m+3)*y^(u-d)=y^u:=by
    rw [←Real.rpow_natCast,←Real.rpow_add y0];congr 1;dsimp only [d];ring
  exact ((abs_sub_le _ (E cut) _).trans (add_le_add first ((abs_sub_comm _ _).le.trans second))).trans_eq
    (by rw [tail];ring)

end YM.Integration.FVA1Physical.Wilson
