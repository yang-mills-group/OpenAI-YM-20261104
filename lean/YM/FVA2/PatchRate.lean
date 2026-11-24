import YM.PertExtension.MeshIntegral
import YM.X.Bare.Subcell
/-!
# Mesh error power estimate on separated compact

 No factor exploding with volume/time. Include exactly `Grid` and `Origins` helpers.
 -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.Sunset
open MeasureTheory Filter Topology Set Finset Function Metric Lattice Extraction
open PertExtension.LatticePT Grid
open scoped Topology ContDiff Classical BigOperators NNReal
variable (q:ℕ+) {n:ℕ}  (h:1<q.val)
local notation "X"=> Points n
local notation "grid"=> Grid.offsets q n
local notation "Z"=> epsilon q
-- strengthen Grid.valid uniformly
include h
theorem rectangle {K:Set (Points n)}(hK:IsCompact K): ∀ᶠ j in atTop,∀ x∈K,x∈Grid.deck q j (Grid.signal q j x):= by
    have H(i:Fin n)(v:Axis): ∀ᶠ k:ℕ in atTop,∀ x∈K, let A:= Extraction.address (epsilon q k) x i v; let N:ℤ:= ( side q k ).val; -N< 2*A ∧ 2*A≤N:= by
        let F(x:X):ℝ:= x i v; have hp:Continuous F:= ( PiLp.continuous_apply 2 _ v ).comp (PiLp.continuous_apply 2 _ i); obtain ⟨R,hR⟩:= hK.exists_bound_of_continuousOn hp.continuousOn; let B:= R+1
        have hv:Tendsto (fun k:ℕ=> ((Z k)⁻¹/((side q k).val:ℕ)) * B) atTop (𝓝 0):=by
            obtain ht:= (side_rate h 1).mul_const B; simpa [epsilon,magnify] using! ht
        filter_upwards [hv.eventually (gt_mem_nhds (show (0:ℝ)<1/3 from by norm_num))] with k hk x hx; let a:= Z k; let y:= Extraction.address a x i v; let N:ℕ:= ( side q k ).val; have he:0<a:=epsilon_pos _ _; have ht:= side q k|>.pos; have hr:0<(N:ℝ):=Nat.cast_pos.mpr ht;
        have hu : |(y:ℝ)| ≤ a⁻¹ * B:= by
            rw [inv_mul_eq_div]; apply ( le_div_iff₀ he ).mpr; rw [ mul_comm ]; rw [← abs_of_pos he,← abs_mul ]; obtain hm:= abs_add_le (a * (y:ℝ) - x i v) (x i v); rw [sub_add_cancel] at hm; linarith only [ show |a * (y:ℝ) - x i v| ≤ a from coord_grid_bound he _ _ _,hm, show a ≤ 1 from PositionX.Bare.Subcell.small q k, show |x i v| ≤ R from hR x hx, sub_add_cancel (a*(y:ℝ)) (x i v), show B=R+1 from rfl] -- rw might changes.M
        have h0:(|(y:ℝ)|)*3<N:= by
             replace hk :(a⁻¹*B)/N <1/3:=by rw [mul_div_right_comm]; exact hk
             rw [div_lt_div_iff₀ hr (by norm_num),one_mul] at hk; linarith
        rw [ ← Int.cast_abs ] at h0; have hw : |y| * 3 < ((side q k).val:ℤ):= by exact_mod_cast h0
        have hge:=le_abs_self y; have hge' :=neg_le_abs y; exact (by omega : -(N:ℤ)< 2*y ∧ 2*y≤(N:ℤ) )
    filter_upwards [ eventually_all.mpr (fun i=> eventually_all.mpr fun j=>H i j) ] with i hi x hx
    change Extraction.address _ _ = _;funext j; exact Eq.symm (lift_eq_iff.mpr ⟨ rfl,fun l=> hi j l x hx ⟩)
-- all centers eventually. no loss from repeated-volume weights
variable {F:Points n→ℝ} {f:∀ i:ℕ, Native q i → Grid.offsets q n i→ℝ} {t:ℕ→ℝ}{B:ℝ}{K:Set ( Points n )}{k:ℝ≥0}
lemma total_mass (h0:∀ x∉K,F x=0)(hK:IsCompact K)(hF:LipschitzWith k F) (hP: ∀ i,epsilon q i≤t i )(hB:0 < B)
   (he:∀ᶠ i in atTop,∀ o∈ origins q i,∀ p:grid i, dist ( f i o p ) ( F ( sample q i p ) ) ≤ B*t i ∧ ( sample q i p ∉ K → f i o p=0 )) : ∃ C:ℝ,0<C∧∀ᶠ i in atTop, ∀ o∈origins q i, dist ( ( epsilon q i ) ^ (4*n) * ∑ p:grid i, f i o p ) (∫ x,F x) ≤ C*t i:= by
    obtain ⟨R,hR⟩:= hK.isBounded.subset_closedBall (0:X); let L:= closedBall (0:X) (R+1); have hL : IsCompact L:= isCompact_closedBall _ _; have HH: Tendsto (fun i:ℕ=> (4*n:ℝ)*epsilon q i) atTop (𝓝 0):= by simpa only [mul_zero] using! (( epsilon_zero h ).mono_right inf_le_left).const_mul (4*n:ℝ)
    let a:ℝ:=B+k*(4*n:ℝ); have ha:a>0:= by unfold a; positivity
    refine ⟨ a*(volume.real L +1), by positivity, ?_ ⟩; filter_upwards [ he, HH.eventually (gt_mem_nhds zero_lt_one), rectangle q h hK ] with i hi hI hT o ho; let A:= stepper i ( f i o ); have hy: Integrable A:= charged _; have ht: Integrable F:= hF.continuous.integrable_of_hasCompactSupport ( IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_ ); swap; · exact closure_minimal (fun x hx=> by_contra (fun h=> hx ( h0 x h ))) hK.isClosed
    rw [← Grid.knot, dist_eq_norm,← integral_sub hy ht]; let r:= t i; have hr:0<r:= lt_of_lt_of_le ( epsilon_pos _ _ ) (hP i)
    have HX(x:X): (A-F) x≠0 → ∃ p:grid i,x∈ deck q i p∧ x∈L:= by
         intro x'; by_cases hx:x∈K; · exact ⟨ Grid.signal q i x, hT _ hx, closedBall_subset_closedBall (show R≤ R+1 from by linarith) (hR hx) ⟩
         by_cases H: ∃ p:grid i,x∈ deck q i p
         · obtain ⟨p,hp⟩:= H; refine ⟨p,hp,?_⟩; have hu : sample q i p∈ K:=by contrapose! x'; change A x-F x=0; unfold A; rw [step_inside hp,(hi _ ho _).2 x',h0 _ hx,sub_zero];
           change dist x 0 ≤ R + 1; exact le_trans (dist_triangle _ (sample q i p) _) (by linarith only [show (4*n:ℝ)* epsilon q i<1 from hI,deck_dist q hp,dist_comm x (sample q i p),show dist (sample q i p) 0≤R from hR hu])
         push Not at H; exact False.elim ( x' (by rw [ Pi.sub_apply, show A x=0 from step_missing H,h0 _ hx, sub_zero ]) )
    change ‖∫ x,(A-F) x‖≤_; rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=L) (f:=A-F) ( fun x hx=> by_contra ( fun h=> hx ((HX x h).choose_spec.2))) ]; apply le_trans ( norm_setIntegral_le_of_norm_le_const ( C:=a*r ) hL.measure_lt_top ?_ ); swap
    · intro x hx; by_cases H:(A-F) x=0; · rw [H,norm_zero]; positivity
      obtain ⟨p,hp,_⟩:= HX x H; let d:= sample q i p; change ‖A x-F x‖ ≤ _; rw [show A x=f i o p from step_inside hp, ← dist_eq_norm ]; apply le_trans ( dist_triangle _ ( F d ) _ ); apply ( add_le_add ( hi o ho p |>.1 ) ( hF.dist_le_mul d x ) ).trans; unfold a; obtain hm:dist d x ≤ (4*n:ℝ)* r:= ( deck_dist q hp ).trans ( mul_le_mul_of_nonneg_left ( hP _ ) (by positivity) ); nlinarith only [hm, show 0≤(k:ℝ) from k.property, show (4*n:ℝ)*r=(4*n:ℝ)*t i from rfl]
    nlinarith only [show (0:ℝ) ≤ volume.real L from by positivity,show 0<a*t i from mul_pos ha hr,show r=t i from rfl]
end YM.FVA2.Sunset
