import YM.FVAAlt2.Moving.Grain
/-!
# Canonical LPT kernels, all smooth profiles at common *moving* regulator schedule
Fixed vertex horizons (subtraction test arity allowed) then ℓ and coadmitted pressures. Does not require
 uniform clearance of operator series lemmas under arbitrary cutoff schedules. Takes COUNTABLY GENERATED filter iff downstream DCT (otherwise preserve piecewise power estimates). Canonical lattice placement point offset at one true origin (keep allowed-clearance class including any such sequence; no center averaging theorem here -- center hard ties in ordinary proof not in this sampler). Supports on any compact separated sets. Grains pay real & complex coefficients post-scaled. Position PS solve late independent of regulator matrix. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Pegs
open Function Set Filter MeasureTheory Real Topology Metric
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT
open MS MS.Land MS.Dial MS.Rake MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open PowerSeries Integration RunFormalChain FormalOPE Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles
open Extraction
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(hG:G.Simple) {K:KernelChoices}{X:Type} (Y:Oracle.Program K) (Z:∀ B:Patch,B.Branches K G) (C:Run G)(R:Lodge.Contract C Y Z)(t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B" => ( R.profile Y Z C t ht )
local notation "P" => ( Period.Field.LodgeT.instance_real Y Z C R t ht )
set_option quotPrecheck false
variable (F:Calibration.Tent ( ( R.profile Y Z C t ht ).entire )){g:G.ColorIndex}(p d:ℕ)
variable {n:ℕ}{u: MS.Local.Physical.Deck G}(D:Fin n→ MS.Rake.Label u)(T:MS.Land.Prescription u){J:Booked u}(H: MS_Data G J) (μ:ℝ)
variable (Λ:X→ℕ)(a:X→ Cover) {φ:Points n→ℝ} (hf:Continuous φ) {E:Set (Points n)}(hE:IsCompact E)(hs:Function.support φ ⊆ E)(hC:E⊆ conf n)
local notation "η" x:max=> ( Sound.Alone (B) x )
local notation:max "θ" x:max=> (μ-(B).Θ x)
local notation "K₀"=> ( grain Y Z C R t ht F D T μ Λ a )
noncomputable def earn (B':Track X) (x:X)(φ:Points n→ℝ)(i:Motor B' n x):ℝ:= (Sound.Alone B' x)^(4*n)*φ (CalendarT.sample x i)
def compilation (B':Track X)(x:X)(K: Motor B' n x→ PowerSeries ℂ)(φ:Points n→ℝ) : PowerSeries ℂ := ∑ u:Motor B' n x, PowerSeries.C ( (↑( earn B' x φ u ):ℂ) ) * K u
-- inherits orientation & ε powers in same position-leg. Camera support.W.Structure Customer.Broader. 
noncomputable abbrev profileθ (φ:Points n→ℝ)(x:X): PowerSeries ℂ:= compilation ( R.profile Y Z C t ht ) x ( grain Y Z C R t ht F D T μ Λ a x ) φ
local notation "Z₁"=> profileθ Y Z C R t ht F D T μ Λ a
local notation:max "α" x:max=> Sound.BudgetAir (B) x
variable (l:Filter X)(hV:Tendsto t l atTop)(hF: Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p)(hver:( R.profile Y Z C t ht ).VenueT a)(Hq:∀ x,p≤t x)(hT:TaylorOKPl H (Lobby.Table (basisR C) u) T)
variable {σ: X→ℕ}(hσ:Sound.Margin (I:=Fin n) Y Z C R t ht F p d T μ σ)(hv:∀ᶠ x in l,σ x ≤ Λ x) (hd:∀ i,( D i ).h≤d)
local notation:max "Y_" k:max => (Home.Profiles.area H D μ k)
lemma antics(j:ℕ)(φ: Points n→ℝ)(i:X): coeff j ( takeReal (Z₁ φ i) )= η i ^ (4*n) *∑ x : Motor B n i,φ (CalendarT.sample i x)* ( coeff j ( K₀ i x ) ).re :=by
 rw [takeReal,PowerSeries.coeff_mk]; unfold profileθ compilation; simp_rw [map_sum,PowerSeries.coeff_C_mul,Complex.re_sum,Finset.mul_sum]; exact Finset.sum_congr rfl fun x _=> by rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,earn,mul_assoc]
lemma systematic {D:Track X}(h:Tendsto D.batch l atTop): Tendsto (Sound.BudgetAir D) l (𝓝 0):= Real.tendsto_exp_atBot.comp (( D.θ_runs h).const_mul_atTop_of_neg (neg_lt_zero.mpr mild_p)) -- k unused remove
open Metric
lemma FieldA {x:Points n}(i:ℕ) (hx:x∈conf n): ContinuousAt ( Y_ i ) x:= (((Dial.contin H D (realize x) (Home.Profiles.realize_one hx) Finset.univ i μ).1).comp realize_s.continuousAt)
include hG hV hF Hq hver hT hσ hv hd
lemma drawn {x:Points n}(hx:x∈ conf n)(j:ℕ)(hj:j≤p)(r:(i:X)→ Motor (R.profile Y Z C t ht) n i)(he:Tendsto (fun i=> CalendarT.sample i (r i)) l (𝓝 x)): Tendsto (fun i=> PowerSeries.coeff j ( K₀ i (r i))) l (𝓝 ( ( Y_ j ) x )) := by
 let u(i:X):= coeff j (K₀ i (r i)); let v(i:X):= CalendarT.sample i (r i)
 have hp:Tendsto (Y_ j∘ v) l (𝓝 ((Y_ j) x)):= (FieldA D H μ j hx).tendsto.comp he
 obtain ⟨s,hs,hP⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (( conf_open n ).mem_nhds hx)
 obtain ⟨C₁,hC,h⟩:= uniform hG Y Z C R t ht F p d D T H μ Λ a (isCompact_closedBall x s) hP l hV hF hver Hq hT hσ hv hd j hj -- shadows H
 have he: Tendsto ( u-Y_ j ∘ v ) l (𝓝 0):= by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ( (( he.eventually (Metric.closedBall_mem_nhds x hs) ).and h ).mono (fun i hi=> hi.2 _ hi.1 ) ); simpa only [mul_zero] using! (systematic l (R.batch_r Y Z C t ht hV)).const_mul C₁
 convert he.add hp using 1; rotate_left
 · rw [zero_add]
 funext t; exact ( sub_add_cancel (u t) (( Y_ j ) (v t)) ).symm
variable [l.NeBot] [l.IsCountablyGenerated]
include hs hE hf hC
lemma valueAt (j:ℕ)(hj:j≤p): Tendsto (fun x=> coeff j ( takeReal ( Z₁ φ x ))) l (𝓝 (coeff j (Home.Profiles.forecast H D μ φ))) := by
 let v:=Y_ j
 let f(x:Points n):= φ x*( v x ).re; let Q(i:X)(x:Motor B n i):= φ (CalendarT.sample i x) * ( coeff j (K₀ i x)).re
 have Hx:= R.batch_r Y Z C t ht hV; have hm:= CalendarT.ports ( B ) Hx
 simp_rw [ antics,Home.Profiles.forecast,PowerSeries.coeff_mk ]; refine ( MeshT.road (K:=E) (F:=Q) (H:=f) hm hE ( ?_ ) ?_ ?_ ?_ ).2
 · intro i hi; exact hs (left_ne_zero_of_mul hi)
 · intro i x h; unfold Q; exact mul_eq_zero_of_left (Function.notMem_support.mp (fun hi=> h (hs hi))) _
 · have hp:ContinuousOn (fun x=> φ x) E:= hf.continuousOn
   obtain ⟨C₀,hC0,h⟩:= uniform hG Y Z C R t ht F p d D T H μ Λ a hE hC l hV hF hver Hq hT hσ hv hd j hj; -- shadow hC!
   obtain ⟨A,hA⟩:= hE.exists_bound_of_continuousOn hp
   obtain ⟨B',hB⟩:= hE.exists_bound_of_continuousOn (f:=v) (fun i hi=>( FieldA D H μ j (hC hi)).continuousWithinAt )
   refine ⟨ (max A 0)*(max B' 0+C₀),by positivity,?_ ⟩; filter_upwards [h,(systematic l Hx).eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with i hi he x hX
   unfold Q; rw [ abs_mul ]; refine mul_le_mul ( ( hA _ hX ).trans ( le_max_left .. )) (?_) (abs_nonneg _) (le_max_right ..);
   refine le_trans (Complex.abs_re_le_norm _) ?_
   calc
     _ ≤ _:= ( norm_le_norm_add_norm_sub (v (CalendarT.sample i x)) ( coeff j ( K₀ i x ) ) ).trans_eq (congr_arg (‖v (CalendarT.sample i x)‖ + ·) ( norm_sub_rev .. )) -- check reg Lemma
     _ ≤ _ := add_le_add ( ( hB _ hX ).trans (le_max_left ..) ) (( hi x hX ).trans (mul_le_of_le_one_right hC0.le (show Sound.BudgetAir B i< 1 from he).le))
 · intro x hx; have hu:= hm.campaign x; exact (hf.continuousAt.tendsto.comp hu).mul ( Complex.continuous_re.continuousAt.tendsto.comp ( drawn hG Y Z C R t ht F p d D T H μ Λ a l hV hF hver Hq hT hσ hv hd (hC hx) _ hj _ hu ) )
end YM.RegulatorIR.FVAAlt2.Moving.Pegs
