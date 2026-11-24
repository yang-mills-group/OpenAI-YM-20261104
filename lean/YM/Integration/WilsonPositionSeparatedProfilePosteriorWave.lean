import YM.Integration.WilsonPositionSeparatedProfileLocalUniform
import YM.Integration.WilsonLocalCompactPosterior

/-! The complete signed physical test on the genuine positive retained compact
posterior at every older gauge, including the held identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfilePosteriorWave
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Tree RG16 Precision PertExtension
open Source Labels RG05Readout.Address RG05Readout.Native OPE.Orbits MergeProof MergeProof.Accent
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open RG05Readout RG05Readout.Pulse WilsonReportingPlaquetteWindows WilsonReportingForestPivots
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonPositionSeparatedProfileLocalPurchase
open WilsonPositionSeparatedProfileLocalWave WilsonLocalCompactPosteriorWeight
open private exchange from YM.Integration.WilsonPositionSeparatedProfileLocalPurchase
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] {m N per:ℕ}

def read (live:m+1<N) (grade:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (h:Config G (R.family.side (m+1) per)→ℝ) :=
  let a:=amount R live grade T (incident R T d o) V
  (∫u,a u*h (T.drape u) ∂T.order G)/(∫u,a u ∂T.order G)

def printed (live:m+1<N) (grade:ℕ) (d:I→ℕ) (t:ℕ) (y:∀i,R.family.label (d i)) (φ:Wave I)
    (r:ℝ) (ξ:Cloud I) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ) (V:Config G (R.family.side m per)) :=
  ∑z:placements (V:=I) R.family (m+1) per t, read R live grade d z.val T V (fun U=>H U*
    mark R d z.val (R.family.path.rep N per (m+1)).p.threshold y (WilsonPositionSeparatedProfileLocalWave.ink R φ r ξ z.val) χ U)

private theorem deviation (live:m<N) (V:Config G (R.family.side m per))
    (h:Config G (R.family.side (m+1) per)→ℝ) {A:ℝ} (hf:∀U,‖h U‖≤A) :
    actualAverage R.family (N:=N) (fun U=>|h U-actualAverage R.family (N:=N) h V|) V≤2*A := by
  have mean:=actualAverage_norm_le R.family R.makes live hf V
  have cap (U):‖|h U-actualAverage R.family (N:=N) h V|‖≤2*A:=by
    rw [Real.norm_eq_abs,abs_abs,←Real.norm_eq_abs]
    exact (norm_sub_le ..).trans (by linarith only [hf U,mean])
  exact (le_abs_self _).trans (actualAverage_norm_le R.family R.makes live cap V)

private theorem bounded (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {δ:ℝ} (dp:0<δ) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      ∀A:ℝ,(∀U,‖H U‖≤A)→δ*regulatorRun R.family N per (m+1)^q≤1→
      |actualAverage R.family (N:=N) H V-read R live grade d o T V H|≤4*(δ*regulatorRun R.family N per (m+1)^q)*A:=by
  filter_upwards [WilsonLocalCompactPosterior.original R simple marks fees slow d q grade ord dp]
    with m sale N live per o T V H env gi A cap limit
  let e:=δ*regulatorRun R.family N per (m+1)^q
  have ep:0≤e:=mul_nonneg dp.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have ap:0≤A:=(norm_nonneg (H 1)).trans (cap _)
  have p:|read R live grade d o T V H-actualAverage R.family (N:=N) H V|≤
      e*(1+e)*actualAverage R.family (N:=N) (fun U=>|H U-actualAverage R.family (N:=N) H V|) V:=
    (sale N live per o T V H env gi).2.2.2.2.2
  rw [abs_sub_comm]
  calc _ ≤ e*(1+e)*(2*A):=p.trans (mul_le_mul_of_nonneg_left (deviation R live.le V H cap) (by positivity))
       _ ≤ e*2*(2*A):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [limit] : 1+e≤2) ep) (by positivity)
       _ = _:=by ring

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (d:I→ℕ) (φ:Wave I) (compact:HasCompactSupport φ.val) (s q grade:ℕ)
    (ord:depth R d s q+5≤grade) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) (per t:ℕ),(t:ℝ)≤R.family.path.levels.clock.hatBeta (m+1)^s →
      ∀(y:∀i,R.family.label (d i)) (r:ℝ) (ξ:Cloud I) (T:Forest (R.family.path.levels.clock.op m per).ratio)
      (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      ∀M:ℝ,(∀U,‖H U‖≤M)→∀V,
      |actualAverage R.family (N:=N) (WilsonPositionSeparatedProfileLocalAssay.field R (N:=N) d t y φ r ξ χ H) V-
        printed R live grade d t y φ r ξ T χ H V|≤
        ε*regulatorRun R.family N per (m+1)^q*(‖χ‖*originalMass R d y)*M := by
  obtain ⟨K,kp,budget⟩:=WilsonPositionSeparatedProfileLocalUniform.original R d φ compact s
  let a:=s*(4*Fintype.card I)+reserve R d
  let h:=q+2*a
  let δ:=min ((2:ℝ)^h)⁻¹ (ε/(4*K*2^a))
  have dp:0<δ:=lt_min (by positivity) (by positivity)
  have cash:4*δ*K*2^a≤ε:=by
    have c:δ*(4*K*2^a)≤ε:=(le_div_iff₀ (by positivity)).mp (min_le_right ..)
    linarith only [c]
  filter_upwards [bounded R simple marks fees slow d h grade ord dp]
    with m sold N live per t small y r ξ T χ H env gi M hM V
  let k:=m+1
  let S:=placements (V:=I) R.family k per t
  let c:=fun z:S=>WilsonPositionSeparatedProfileLocalWave.ink R φ r ξ z.val
  let θ:=(R.family.path.rep N per k).p.threshold
  let Z:=fun z:S=>mark R d z.val θ y (c z) χ
  let F:=fun z:S=>fun U=>H U*Z z U
  let g:=regulatorRun R.family N per k
  let b:=R.family.path.levels.clock.hatBeta k
  let X:=‖χ‖*originalMass R d y
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have bp:1≤b:=(R.family.path.levels.fits.delayed k).le
  have gb:g≤2:=by
    have bb:b*g^2≤2:=by simpa only [pow_one,pow_zero,mul_one,Nat.zero_add] using exchange R per live.le 0 1
    have b2:g^2≤2:=(by nlinarith only [mul_le_mul_of_nonneg_right bp (sq_nonneg g)] : g^2≤b*g^2).trans bb
    nlinarith only [b2,sq_nonneg (g-1)]
  have limit:δ*g^h≤1:=by
    calc _ ≤ ((2:ℝ)^h)⁻¹*2^h:=mul_le_mul (min_le_left ..) (pow_le_pow_left₀ gp gb h) (pow_nonneg gp _) (by positivity)
         _ = 1:=inv_mul_cancel₀ (by positivity)
  have mp:0≤M:=(norm_nonneg (H 1)).trans (hM _)
  have xp:0≤X:=mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _)
  obtain ⟨A,ap,cap,total⟩:=budget k N per live.le t small y r ξ χ H M hM
  have fe (z:S):Envelope (F z):=env.mul (legitimate R d z.val θ y (c z) χ).1
  have fg (z:S):GaugeInvariant (F z):=by
    intro a U;exact congrArg₂ (·*·) (gi a U) ((legitimate R d z.val θ y (c z) χ).2 a U)
  have sum : actualAverage R.family (N:=N) (WilsonPositionSeparatedProfileLocalAssay.field R (N:=N) d t y φ r ξ χ H) V=
      ∑z:S,actualAverage R.family (N:=N) (F z) V := by
    have integrable (z:S):Integrable (fun U=>actualConditionalDensity R.family N per m V U • F z U) (prior G _):=
      actualAverage_integrable R.family R.makes live.le (fe z).meas.aestronglyMeasurable (cap z) V
    unfold actualAverage;rw [←integral_finsetSum _ fun z _=>integrable z]
    apply integral_congr_ae;filter_upwards with U
    simp only [WilsonPositionSeparatedProfileLocalAssay.field,WilsonPositionSeparatedProfileReportingPrimary.read,map_sum,Finset.mul_sum,Finset.smul_sum];rfl
  have each (z:S):|actualAverage R.family (N:=N) (F z) V-read R live grade d z.val T V (F z)|≤4*(δ*g^h)*A :=
    sold N live per z.val T V (F z) (fe z) (fg z) A (cap z) limit
  rw [sum,printed,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑z:S,4*(δ*g^h)*A:=(Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z _=>each z)
    _ = 4*δ*g^h*((Fintype.card S:ℝ)*A):=by rw [Finset.sum_const,card_univ,nsmul_eq_mul];ring
    _ ≤ 4*δ*g^h*(K*b^a*X*M):=mul_le_mul_of_nonneg_left total (by positivity)
    _ = (4*δ*K)*(b^a*g^(q+2*a))*X*M:=by dsimp only [h];ring
    _ ≤ (4*δ*K)*(2^a*g^q)*X*M:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exchange R per live.le q a) (by positivity)) xp) mp
    _ ≤ _:=by calc _ = ((4*δ*K*2^a)*g^q)*X*M:=by ring
                   _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cash (pow_nonneg gp _)) xp) mp

end YM.Integration.WilsonPositionSeparatedProfilePosteriorWave
