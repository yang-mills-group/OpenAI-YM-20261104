import YM.FVA2.O.Read.Point
/-!
# Smear a finite bundle of evaluation functions to reproduce point values exactly
 By finite-dimensional density. For positivity of leading reflected matrix; this only
 fixes which far tests to use, does not define PT scheme from OPE values.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G:Gauge }{ I: Type }{n m d:ℕ}{ x:Points n }{ s:Opens ( Points n ) }
abbrev RealU {n:ℕ}(s:Opens ( Points n )) := TestFunction s ℝ ⊤
variable {F:I→ Points n→ℂ} {f:Points n→ℂ}
abbrev money (t:RealU s)(f:Points n→ℂ):= ∫ x:Points n,t x • f x
lemma tent (t:RealU s)(h:ContinuousOn f s): Integrable ( fun i=> t i • f i ):= by
    let g i:= t i • f i; let T:=tsupport t; rw [show (fun x=> t x • f x)=T.indicator g from ?_];
    · exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr ( ( t.continuous.continuousOn.smul (h.mono t.tsupport_subset) ).integrableOn_compact t.hasCompactSupport )
    funext i; by_cases hi:i∈T; · exact ( indicator_of_mem hi g ).symm
    rw [indicator_of_notMem hi, image_eq_zero_of_notMem_tsupport hi, zero_smul ]
def atlas (F:I→ Points n→ℂ)(h:∀ i,ContinuousOn ( F i ) s) : RealU s →ₗ[ℝ] I→ℂ := {
    toFun p i:= money p ( F i )
    map_add' a b:= by funext i; unfold money; rw [ Pi.add_apply ]; simp_rw [ add_apply, add_smul ]; exact integral_add ( tent a ( h i ) ) ( tent b ( h i ) )
    map_smul' c p:= by funext i; unfold money; rw [Pi.smul_apply]; simp_rw [ smul_apply,smul_eq_mul,mul_smul ]; exact integral_smul c (fun x=>p x • F i x) }
namespace Candle
abbrev Lit (s: Opens (Points n))(x:Points n):= { t:ContDiffBump x // tsupport ( t.normed volume )⊆ (s:Set ( Points n )) }
lemma supportV (t:ContDiffBump x) : tsupport ( t.normed volume ) = tsupport t:= by unfold tsupport; rw [ t.support_normed_eq,t.support_eq ]
lemma lights (h:x∈s): ∃ T:ℕ→ Lit s x,Tendsto (fun i=> ( T i ).val.rOut ) atTop (𝓝 0):= by
    obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp ( s.isOpen.mem_nhds (show x∈ ( s:Set (Points n) ) from h) ); let A (i:ℕ):= r/((i:ℝ)+2); have hA (i): 0<A i:= by unfold A; positivity
    let V(i): ContDiffBump x:= ⟨A i/2,A i,half_pos (hA i),half_lt_self (hA i)⟩; have hv(i:ℕ): A i < r:= by unfold A; rw [div_lt_iff₀ ( by positivity ) ]; nlinarith [ Nat.cast_nonneg (α:=ℝ) i ]
    refine ⟨ fun i=> ⟨V i,(show _ from ?_ )⟩,?_⟩
    · rw [ supportV ( V i ), ( V i ).tsupport_eq ]; exact subset_trans ( closedBall_subset_ball ( hv i ) ) hR
    exact tendsto_const_nhds.div_atTop ( tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop )
def gel (k: Lit s x): RealU s:= ⟨ k.val.normed volume,k.val.contDiff_normed,k.val.hasCompactSupport_normed,k.property ⟩
lemma pricy {T:ℕ→Lit s x}(h:Tendsto ( fun i=> ( T i ).val.rOut ) atTop (𝓝 0))(he: x∈s)(hp:ContinuousOn f s): Tendsto ( fun i=> money ( gel ( T i )) f ) atTop (𝓝 ( f x )) := by
    refine Metric.tendsto_nhds.mpr (fun ε hε=>?_ ); obtain ⟨δ,hδ,hD⟩:= Metric.continuousAt_iff.mp ( hp.continuousAt ( s.isOpen.mem_nhds ( show x∈(s:Set (Points n)) from he ) ) ) (ε/2) ( half_pos hε ); filter_upwards [ h.eventually ( gt_mem_nhds hδ ) ] with i ht
    let q:= ( T i ).val; let v:= q.normed volume; let P:Points n→ℂ:= fun x=> v x • f x; change dist (∫ z, P z) ( f x ) < ε; have hP : Integrable P := tent ( gel ( T i ) ) hp; have hv: Integrable v := q.integrable_normed; have hI : ∫ x, v x= (1:ℝ):= q.integral_normed;
    calc
      _ = ‖∫ z:Points n,P z - v z • f x‖ := ( by rw [ dist_eq_norm, integral_sub hP ( hv.smul_const .. ), integral_smul_const, hI,one_smul ] )
      _ ≤ ∫ z:Points n, ‖P z - v z • f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z:Points n, v z*(ε/2) := by
           apply integral_mono ( hP.sub (hv.smul_const ( f x )) ).norm (hv.mul_const _); intro j; have he:0≤ v j:= q.nonneg_normed j; change ‖v j • f j - v j • f x‖ ≤ _; rw [ ← smul_sub,norm_smul,norm_of_nonneg he ]; by_cases h:v j=0; · dsimp only; rw [h,zero_mul,zero_mul]
           refine mul_le_mul_of_nonneg_left ?_ he; rw [← dist_eq_norm]; exact ( hD ( lt_trans ( mem_ball.mp ( q.support_normed_eq ( μ:=volume ) ▸ h ) ) ht ) ).le
      _ < ε := by rw [ integral_mul_const,hI,one_mul ]; linarith
end Candle
variable [Fintype I]
theorem funds_R (hx:x∈s)(hf:∀ i,ContinuousOn ( F i ) s): ∃ T:RealU s,∀ i, money T ( F i )= F i x:= by
    obtain ⟨T,hT⟩:= Candle.lights hx; let L:= atlas F hf; have h : Tendsto (fun i=> L ( Candle.gel ( T i ) )) atTop (𝓝 ( fun i=> F i x )):= tendsto_pi_nhds.mpr ( fun i=> Candle.pricy hT hx ( hf i ) ); have hp:(fun i=> F i x)∈ L.range:= L.range.closed_of_finiteDimensional.mem_of_tendsto h ( Eventually.of_forall (fun i=> LinearMap.mem_range_self _ _ ) ); obtain ⟨k,hk⟩:= hp; exact ⟨ k,congr_fun hk ⟩
end YM.FVA2.O.Read

