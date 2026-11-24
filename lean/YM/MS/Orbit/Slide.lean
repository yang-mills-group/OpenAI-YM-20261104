import YM.MS.Orbit.Branch
/-!
# Finite-site sum reads the periodic unfolded lattice smooth kernels exactly. Deck deperiod.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City
open scoped Topology ContDiff Interval
variable {n:Side}{p:Site n}{F:QP→ℂ}{x:Cover}
def totalS (n:Side):= rail ( ψstep n )
instance (n:Side): IsLocallyFiniteMeasure (totalS n) := by
    constructor; intro p; let b:= ψstep n; refine ⟨ ball p 1, ball_mem_nhds _ zero_lt_one,?_ ⟩; change Measure.map (Tick b) planeF (ball p 1) < _; rw [Measure.map_apply tick_m measurableSet_ball]; apply lt_of_le_of_lt _ ( measure_ball_lt_top (μ:=planeF) ( x:=p ) (r:=(b+1)) ); apply measure_mono; intro q hp; obtain ht:= maxS (ψpp n) q; have hh : dist (Tick b q) p < 1:= hp; apply lt_of_le_of_lt (dist_triangle q (Tick b q) p); exact add_lt_add_of_le_of_lt ( (by rwa [dist_comm, dist_eq_norm] : dist q (Tick b q) ≤ b)) hh
lemma total_eq (n:Side): totalS n=Measure.sum (fun i:Cover=> ENNReal.ofReal ( νt n ) • Measure.dirac ( walk n i )):= by simp_rw [totalS, Rview ( ψpp n ),τ_amount,η_walk]
lemma wide_c (n:Side): Coasts (totalS n):= fun i=> by rw [← natural n i,η_walk]; exact boom ( ψpp n ) _ -- syntax
-- reps in positive deck
abbrev porch (x:Site n): Cover:= fun i=> (x i).val
lemma porch_w (x:Site n): wrap n (porch x)=x:= by funext i; change ((↑ ((x i|>.val):ℤ)):Per n) = _; simp -- ZMod
lemma whereB (x:Cover): walk n x∈deck↔ ∀ i:Axis,0≤ x i ∧ x i < n.val := by
   rw [Fiddle.deck, shellsB rising,η_walk]; simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ico, at_whole]; obtain ht:= ψpp n; have hh:= Bloch.side_pos n; have he:tier = ψstep n*(n.val:ℝ):=(div_mul_cancel₀ _ hh.ne').symm
   refine forall_congr' (fun i=>?_); rw [ mul_nonneg_iff_of_pos_left ht,he, mul_lt_mul_iff_right₀ ht ]; norm_cast -- right lemma direction?_he loop
lemma stoop (p:Site n): walk n (porch p)∈deck:= whereB _|>.mpr (fun i=> ⟨Int.natCast_nonneg _, by exact_mod_cast ZMod.val_lt (p i)⟩)
lemma lived (x:Cover)(h:walk n x∈ deck): x=porch (wrap n x):= by funext i; change _=(((x i:Per n).val):ℤ); rw [ ZMod.val_intCast, Int.emod_eq_of_lt ]; exact (whereB x|>.mp h i).1; exact (whereB x|>.mp h i).2
lemma snipped (n:Side): (totalS n).restrict deck= ∑ i:Site n, ENNReal.ofReal (νt n) • Measure.dirac ( walk n (porch i) ):= by
    classical
    rw [total_eq,Measure.restrict_sum_of_countable]; let A:= ENNReal.ofReal ( νt n ); ext S hS; rw [Measure.sum_apply _ hS,Measure.finsetSum_apply]; let F(x:Cover):=A • Measure.dirac (walk n x); let Q:= Finset.image ( fun p:Site n=> porch p ) univ; rw [tsum_eq_sum (s:=Q) (fun i hi=>?_), Finset.sum_image ?inj]; case inj=> exact fun i _ j _ h=> by simpa only [porch_w] using congr_arg (wrap n) h
    apply Finset.sum_congr rfl; intro i hi; simp_rw [Measure.restrict_smul, restrict_dirac (a:= (walk n) _), if_pos (stoop i)]; -- $Dir simp.
    · rw [Measure.restrict_smul, restrict_dirac, if_neg (fun h=>hi (lived i h ▸ (mem_image_of_mem (fun p:Site n=> porch p ) (mem_univ (wrap n i))))), smul_zero]; rfl
lemma slides (n:Side) (x:Site n) : congrQ (walk n (porch x)) ( Coord x ):= congrQ.out (by rw [porch_w, wrap_lift])
-- sums
abbrev totalW (F:QP→ℂ)(n:Side):= νt n • (∑ i:Site n,F (Coord i) )
lemma deck_bill (h:pinQ F)(n:Side): ∫ i in deck,F i∂ totalS n= totalW F n:= by
    rw [snipped,integral_finsetSum_measure]; simp_rw [integral_smul_measure, integral_dirac, h (slides n _), ← Finset.smul_sum]; rw [ENNReal.toReal_ofReal ( ν_pos n ).le]; -- order.N_S
    intro i _; exact (integrable_dirac (by finiteness)).smul_measure (by finiteness) -- function integrable no condition?
lemma smoothP (h:pinQ F)(hp:Continuous F)(n:Side): ∫ i,(aisle i:ℂ)*F i ∂totalS n =totalW F n:= ( crystal (μ:= totalS n) (wide_c n) (pin_C h) (Continuous.integrable_of_hasCompactSupport (door_sm.continuous.smul hp) (door_p.smul_right) ) )|>.trans (deck_bill h n)
end YM.MS.Orbit
