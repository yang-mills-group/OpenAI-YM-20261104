import YM.FVA2.PatchRate
import YM.FVA2.PlateP
import YM.FVA2.SmoothPoint
/-!
# Profile smearing with a positive spacing rate. No bare-power divergences.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 860000
namespace YM.FVA2.Spring
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Bare.Subcell
open Lattice Gauge PertExtension PertExtension.Chart PertExtension.LatticePT
open MS MS.Menus MS.Land MS.Theater MS.Tone MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open ColorCode Attend BoxOffice Counterpart Blaze Frost ArchTurn
open PowerSeries WorldJet Pond Fountain
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {Q: Booked (wings G)}(V:Warehouse G) (P: Prescription (wings G))(M:MS_Data G Q)
variable (H:ExactSpin V P)(HI:Trusted P) (he: MixedStory.AllProfiles M V P)
variable {m d:ℕ}(q:ℕ+)(hq:1 < q.val) (j:ℕ) (μ:ℝ)
local notation "Y"=> V.F
local notation "I"=> Fin m
local notation "Ω"=> sameAxis V.F d
local notation "Ξ"=> tuition V P H HI q
variable (v: Test m)(X:Fin m→ E V.F d)
local notation "Z"=> LatticePT.epsilon q
local notation "ψ"=> Pond.clock q
open scoped NNReal
lemma smoothShape (i:ℕ) : ContDiffOn ℝ ∞ (fun x:Points m=>phys V M μ i x d X) ( conf m ) := by
    let K:= conf m; let c:= Poesy.vicinity (Fin m); have he: ContDiff ℝ ∞ ( metric (m:=m) ):= contDiff_pi.mpr (fun i=> Theater.out.toContinuousLinearEquiv.contDiff.comp ( ( ContinuousLinearMap.proj ( R:=ℝ ) (φ:=fun _:Fin m=>E4) i ).contDiff.comp (( PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin m=>E4) ).contDiff) ) );
    unfold phys; simp_rw [ fun z :Points m=> PositionX.Bare.spread_value (sameAxis V.F d) (fun w=> score M μ i w z) X ]; exact ContDiffOn.sum (fun w _=> contDiffOn_const.mul (( Poesy.tourSmooth ( S:=M ) Finset.univ i (pant w) μ).comp he.contDiffOn (fun _ h=> metric_conf h)))
local notation "L"=> (valley (tsupport v))
private abbrev sweepΩ (ε:ℝ) (x: Points m):ℂ:= (sweep (Complex.re ∘ v) ε x:ℂ)+Complex.I*(sweep (Complex.im ∘ v) ε x:ℂ)
lemma combo (k:ℕ)(o:LatticePT.Native q k)(x: Grid.offsets q m k) : prem V P H HI q μ v X k j o x=sweepΩ v (Z k) (Grid.sample q k x) * coeff j ( Ξ k μ o x d X ):= rfl
-- full integrable complex sweep
lemma regard (a:ℝ)(p:Points m): sweepΩ v a p= ∫ x in PositionX.Bare.Subcell.cube,v (p-a • delta m x):= by
    let F(x:PositionX.Bare.Subcell.Space):= v (p-a • delta m x); let x:= ∫ x in PositionX.Bare.Subcell.cube,F x; have hF: IntegrableOn F PositionX.Bare.Subcell.cube:= ( show Continuous F from v.continuous.comp (Continuous.sub ( f:=fun p':PositionX.Bare.Subcell.Space=>p ) continuous_const ( Continuous.const_smul continuousDelta a )) ).continuousOn.integrableOn_compact closedCube; change _ = x; rw [← x.re_add_im]; unfold sweepΩ sweep; have hh (K:ℂ→L[ℝ]ℝ): K x=∫ x in PositionX.Bare.Subcell.cube,K ( F x ) := ( K.integral_comp_comm hF ).symm; rw [show x.re=_ from hh Complex.reCLM,show x.im=_ from hh Complex.imCLM, mul_comm Complex.I ]; rfl
lemma masked (t:ℕ)(a:Points m)(hp:a ∉ L ): sweepΩ v (Z t) a=0:=by
    have hv(E:ℂ→L[ℝ]ℝ): sweep (E ∘ v) (Z t) a= 0:= sweep_in ⟨(epsilon_pos q t).le,PositionX.Bare.Subcell.small q t⟩ ( fun x hz=> by_contra (fun hc=>hz (subset_closure (fun ht=> hc (by rw [comp_apply,ht,map_zero ]))))) hp; unfold sweepΩ; rw [ show sweep (Complex.re ∘ v) _ _=_ from hv Complex.reCLM, show sweep (Complex.im ∘ v) _ _=_ from hv Complex.imCLM ]; simp
lemma appraisal : ∃ c:ℝ,0≤c ∧∀ x:Points m,∀ i, ‖sweepΩ v (Z i) x-v x‖≤c*Z i:= by
    obtain ⟨ K,hK⟩:= ContDiff.lipschitzWith_of_hasCompactSupport v.hasCompactSupport v.contDiff (by simp); obtain ⟨ C,hC⟩:= closedCube.exists_bound_of_continuousOn ( continuousDelta ( n:=m ) ).continuousOn; have hp:C≥0:= le_trans ( norm_nonneg _ ) ( hC 0 ⟨le_rfl,zero_le_one⟩ ); refine ⟨ K*C,by positivity,fun x i=>?_ ⟩; let F(y:PositionX.Bare.Subcell.Space):= v (x- Z i • delta m y); let U:=PositionX.Bare.Subcell.cube; have hF: IntegrableOn F U:= ( show Continuous F from v.continuous.comp (Continuous.sub ( f:=fun p':PositionX.Bare.Subcell.Space=>x ) continuous_const ( Continuous.const_smul continuousDelta (Z i) )) ).continuousOn.integrableOn_compact closedCube;
    let ζ :ℝ:=K*C*( Z i ); rw [ regard ]; change ‖( ∫ y in U,F y ) - v x‖ ≤ ζ; rw [ ← show (∫ _ in U,v x)=v x from (by rw [ setIntegral_const, show volume.real U=1 from volumeOne, one_smul ]), ← integral_sub hF (integrableOn_const closedCube.measure_ne_top) ]; apply ( norm_setIntegral_le_of_norm_le_const ( C:=ζ ) closedCube.measure_lt_top ?_ ).trans_eq ( show ζ* volume.real U= _ from volumeOne ▸ mul_one ζ ); intro t ht; apply ( hK.norm_sub_le _ x ).trans; rw [ sub_right_comm,sub_self, zero_sub,norm_neg,norm_smul_of_nonneg (epsilon_pos q i).le ]; exact ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( hC t ht ) ( epsilon_pos q i ).le ) (by positivity) ).trans_eq (by unfold ζ; ring) -- needs <= target not trans_eq? type
lemma supportΩ : ∃ c:ℝ,0≤c∧∀ x i, ‖sweepΩ v ( Z i ) x‖≤c:= by
    obtain ⟨ c,hc⟩:= v.continuous.bounded_above_of_compact_support v.hasCompactSupport; refine ⟨ c,( norm_nonneg _ ).trans ( hc 0 ),fun x i=>?_ ⟩; rw [regard]; exact ( norm_setIntegral_le_of_norm_le_const closedCube.measure_lt_top (fun _ _=> hc _) ).trans_eq (by rw [volumeOne,mul_one])
lemma feels (t:ℕ):epsilon q t ≤ feel q t:= by
    rw [Pond.ticket ]; apply Real.exp_monotone; have hv:mildG≤1:=by norm_num
    nlinarith [ lights q t ]
include he hq
lemma realizations (M':ℂ→L[ℝ]ℝ) : ∃ C:ℝ,0<C∧∀ᶠ k:ℕ in atTop, ∀ o ∈ origins q k, dist ( ( Z k ) ^(4*m)* ∑ u:Grid.offsets q m k,M' ( prem V P H HI q μ v X k j o u ) ) (M' ( ms V M μ d j m v X )) ≤ C*feel q k:= by
    let P':=prem V P H HI q μ v X; let K(z:Points m):= phys V M μ j z d X; let A:= M' ∘ ((v:Points m→ℂ)*K); obtain ht: L ⊆ conf m:= valley_conf v.tsupport_subset; obtain hC:IsCompact L:= valley_compact v.hasCompactSupport; rw [ invoice,Test.applyTo,← M'.integral_comp_comm ( payable V M μ v X j ) ];
    obtain hx: ContDiff ℝ ∞ ((v:Points m→ℂ)* K):= by
        apply contDiff_iff_contDiffAt.mpr; intro x; by_cases h : x ∈ conf m; · exact v.contDiff.contDiffAt.mul ((smoothShape V M μ X j).contDiffAt ((conf_open m).mem_nhds h))
        have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport v := isOpen_compl_iff.mpr (isClosed_tsupport _) |>.mem_nhds (show x ∈ (tsupport v)ᶜ from fun w => h (v.tsupport_subset w)); apply (contDiffAt_const ( c:=(0:ℂ) )).congr_of_eventuallyEq; filter_upwards [he] with y hy; rw [ Pi.mul_apply,show v y=0 from image_eq_zero_of_notMem_tsupport hy,zero_mul];
    obtain ⟨n,hB⟩:= ContDiff.lipschitzWith_of_hasCompactSupport ((( v.hasCompactSupport).mul_right (f':=K)).comp_left ( map_zero M' )) (M'.contDiff.comp hx) (by simp);
    obtain ⟨c,hc,u⟩:= Fountain.rate_point V P M H HI he q hq μ ht hC j X; obtain ⟨A',hp,h'⟩:= appraisal q v; obtain ⟨B,hN,hM⟩:= supportΩ q v; let v':ℝ→ℂ:=Complex.ofReal; obtain ⟨E,hE⟩:= hC.exists_bound_of_continuousOn ((smoothShape V M μ X j).continuousOn.mono ht); let K':=max E 0; let D:ℝ:= ‖M'‖*( B*c+A'* K' )+1; have hD : D>0:= by unfold D K'; positivity;
    have h0(x:Points m)(hi:x ∉ L):v x=0:= image_eq_zero_of_notMem_tsupport (fun h=> hi ( includes _ h ));
    change ∃ C:ℝ,_ ∧ ∀ᶠ k:ℕ in atTop, ∀ o ∈ origins q k, dist ( _ * ∑ u:Grid.offsets q m k, _ ) (∫ x,A x) ≤ C * feel q k; refine Sunset.total_mass q hq (K:=L) ?_ hC hB ( feels q ) hD ?_; -- syntax
    · intro x hx; simp [A, comp_apply,h0 x hx ] -- A etc.
    filter_upwards [u] with i hu o ho x; let p:=Grid.sample q i x; by_cases H':p∉ L
    · have Hx: prem V P H HI q μ v X i j o x=0:= by rw [ combo ]; change sweepΩ v _ p*_=_; rw [masked q v i p H',zero_mul]
      have h'A: A p=0:= by simp [A, h0 p H']
      change dist _ ( A p ) ≤ _ ∧ _; rw [Hx,h'A,map_zero,dist_self ]; exact ⟨ mul_nonneg hD.le ( cost_pos .. |>.le ),fun _=> rfl ⟩
    refine ⟨?_,fun h=>( H' h ).elim⟩; let a:= sweepΩ v (Z i) p; let b:= PowerSeries.coeff j ( Ξ i μ o x d X ); let r:= feel q i; have hK:= Classical.byContradiction H';
    rw [ combo, dist_eq_norm ]; change ‖M' (a*b)-M' (v p * K p)‖ ≤ _; rw [ ← map_sub ]; apply le_trans (M'.le_opNorm _) ;
    have hz : ‖b-K p‖ ≤ c*r:= by rw [ ← dist_eq_norm ]; exact hu _ ho _ hK;
    have hc' : ‖a*b-v p*K p‖ ≤ (B*c+A'*K')*r:= by
        have hh :‖ a-v p‖≤ A' * r:= ( h' p i ).trans (mul_le_mul_of_nonneg_left (feels q i) hp ); have hm : ‖ K p‖≤K':= (hE p hK).trans (le_max_left ..);
        rw [show a*b-_=_ from (by ring:a*b-v p*K p=a*(b-K p)+(a-v p)*K p) ]; exact ( norm_add_le .. ).trans (le_trans ( add_le_add ( le_trans (norm_mul ..|>.le) (mul_le_mul (hM p i) hz (norm_nonneg _) hN)) ( le_trans (norm_mul ..|>.le) (mul_le_mul hh hm (norm_nonneg _) ( (norm_nonneg _ ).trans hh )))) ( le_of_eq (by ring) ) )
    apply ( mul_le_mul_of_nonneg_left hc' (norm_nonneg M') ).trans; have hp : r>0:= cost_pos ..; change _ ≤ _*r; unfold D; linarith
lemma pooled (R:ℂ→L[ℝ]ℝ): ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop, ‖R (changedWorld V P H HI q i (μ-Pond.clock q i) d j m v X)-R ( ms V M μ d j m v X )‖ ≤ C*feel q i:= by
    obtain ⟨C,h,hv⟩:= realizations V P M H HI he q hq j μ v X R; refine ⟨ C,h,?_⟩; filter_upwards [hv] with i hi;
    rw [ green ]; let U:= origins q i; let c:ℝ:= U.card; let z:= R ( ms V M μ d j m v X ); let a:= C*feel q i; let f(o:LatticePT.Native q i):= (Z i)^(4*m)*∑ u:Grid.offsets q m i,R ( prem V P H HI q μ v X i j o u ); have hh: c>0:= Nat.cast_pos.mpr ( Finset.card_pos.mpr ( hasOrigin q i ));
    change ‖c⁻¹ * (∑ o∈ U,f o) - z‖ ≤ _; rw [show c⁻¹ * _- z=c⁻¹ * ∑ i∈U,(f i-z) from ?_, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le) ]; apply le_trans ( mul_le_mul_of_nonneg_left (( norm_sum_le .. ).trans ( Finset.sum_le_sum (fun s hs=> show ‖f s-z‖ ≤ a from (by rw [ ← dist_eq_norm ]; exact hi s hs)))) ( inv_nonneg.mpr hh.le ) ) ; apply le_of_eq; rw [ Finset.sum_const,nsmul_eq_mul,← mul_assoc, show c⁻¹*U.card=1 from inv_mul_cancel₀ hh.ne', one_mul ]; rw [ Finset.sum_sub_distrib, Finset.sum_const,nsmul_eq_mul, mul_sub,← mul_assoc, show c⁻¹*U.card=1 from inv_mul_cancel₀ hh.ne',one_mul ]
theorem limits_power : ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop, ‖changedWorld V P H HI q i (μ-Pond.clock q i) d j m v X-ms V M μ d j m v X‖ ≤ C*feel q i:= by
    obtain ⟨A,hA,hV⟩:= pooled V P M H HI he q hq j μ v X Complex.reCLM; obtain ⟨B,hB,hY⟩:= pooled V P M H HI he q hq j μ v X Complex.imCLM; refine ⟨ A+B, by positivity,?_ ⟩;
    filter_upwards [hV,hY] with i hx hy; let z:= changedWorld V P H HI q i (μ-Pond.clock q i) d j m v X-ms V M μ d j m v X; rw [ ← map_sub ] at hx hy; change ‖z‖≤_; apply le_trans ( Complex.norm_le_abs_re_add_abs_im .. ); rw [ add_mul ]; exact add_le_add hx hy
end YM.FVA2.Spring
