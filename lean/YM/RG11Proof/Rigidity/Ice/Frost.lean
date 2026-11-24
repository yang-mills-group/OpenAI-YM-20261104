import YM.RG11Proof.Rigidity.Ice.Dawn

/-!
# Euclidean frame path locally cost-free on the associated graded
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position Gauge
open scoped Classical BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y"=>V→L[ℝ] V

lemma withdraw {b:Buffer F d}(h:Frigid b)(hd:6≤d)(hG:G.Simple): ∀ᶠ t:ℝ in 𝓝 0, Feasible b t 1 := by
  by_contra hk
  have hh : ∃ᶠ t:ℝ in 𝓝 0, ¬ Feasible b t 1:=by change ¬∀ᶠ t in 𝓝 0, ¬¬ Feasible b t 1; simpa only [not_not] using hk
  obtain ⟨u,hu,hF⟩:= frequently_iff_seq_forall.mp hh
  choose P hP using fun i:ℕ=>rolling h (show 4≤d by omega) hG (u i)
  obtain ⟨U,hU,g,hg,hL⟩ := (isCompact_closedBall (0:Y) 1).tendsto_subseq fun i=> ice_ball (hP i).1
  have ht: Tendsto (u ∘ g) atTop (𝓝 0):=hu.comp hg.tendsto_atTop
  let M:= P ∘ g
  rw [show U=1 from winner_limit _ ht M (fun i=>hP _) hL] at hL
  let r (i:ℕ):= ‖M i-1‖⁻¹
  let D (i:ℕ) := r i • (M i-1)
  have hK (i : ℕ) : D i∈ Metric.sphere (0:Y) 1:= by
    have hp : ‖M i-1‖≠0:= norm_ne_zero_iff.mpr (sub_ne_zero.mpr (show M i≠1 from by intro he; have H := (hP (g i)).1; rw [show P (g i)=1 from he] at H; exact hF (g i) H))
    rw [Metric.mem_sphere,dist_zero_right]; unfold D r; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel₀ hp]
  obtain ⟨Q,hQ,f,hf,hY⟩ := (isCompact_sphere (0:Y) 1).tendsto_subseq hK
  have hz:Q=0:= rises hd hG (fun i=> hP (g (f i))) (hL.comp hf.tendsto_atTop) (r:=fun i=>r (f i)) hY
  simp [hz] at hQ


-- low cap: no f probe needed because all leading color tests are already
-- orthogonal invariants.
private lemma small_fixed (O : Wheel G) (p : WickPol G)(h:p∈shellSector G 5)(hG:G.Simple)(A:TaylorTower G):
    probe (films (steers O) A) p = probe A p := by
  let f:= (probe (films (steers O) A)).toLinearMap - (probe A).toLinearMap
  apply sub_eq_zero.mp
  suffices shellSector G 5 ≤ LinearMap.ker f from this h
  rw [five_support hG,low_support hG]
  refine sup_le (sup_le (Submodule.span_le.mpr ?_) ?_) ?_
  · intro x hx; rw [show x=1 from hx]; exact sub_eq_zero.mpr ((map_one (probe _)).trans (map_one (probe A)).symm)
  all_goals apply Submodule.span_le.mpr; rintro x ⟨a,c,rfl⟩; apply sub_eq_zero.mpr; change probe _ (team _ _ _)=probe _ (team _ _ _); simp only [basicTeam,films,shows_film]; exact congr_arg ((↑):ℝ→ℂ) (O.inner_map_map ..)

lemma five_comply {b:Buffer F 5} (h: Frigid b)(hG:G.Simple)(t:ℝ): Feasible b t 1 := by
  obtain ⟨O,hO⟩:= h.feasible (by omega) hG t
  constructor
  · intro x y; rfl
  intro i Q
  have ht:= hO.2 i (films (steers O.symm) Q)
  rw [reel_film,show (steers O).comp (steers O.symm)=(.id ℝ V) from ContinuousLinearMap.ext fun x=> O.apply_symm_apply x] at ht
  refine Eq.trans ?_ ht
  have hh : writes F 5 i.v ∈ shellSector G 5:= (exactField F _ _).property
  change probe _ (MvPolynomial.weightedHomogeneousComponent _ _ _) = probe _ (MvPolynomial.weightedHomogeneousComponent _ _ _)
  rw [MvPolynomial.weightedHomogeneousComponent_eq_self i.gr,small_fixed O.symm _ hh hG Q]

lemma tepid {b:Buffer F d}(h:Frigid b)(hd : 4<d)(hG:G.Simple): ∀ᶠ t in 𝓝 0,Feasible b t 1:=by
  rcases eq_or_lt_of_le (show 5≤d from hd) with rfl|h₁
  · exact Eventually.of_forall (five_comply h hG)
  exact withdraw h h₁ hG

lemma Frigid.top_zero {b:Buffer F d}(H : Frigid b)(hG:G.Simple)(hd:4<d)(i:News F d): Reads.top i.n (writes F d (b.val i.v))=0 := by
  apply Maxwell.equalPol; intro A
  let L:= ((quoteL F (d:=d) i.n A).restrictScalars ℝ).toContinuousLinearMap
  have hp : HasDerivAt (fun t:ℝ=> L (drive b.val i.v t)) (L (b.val i.v)) 0:= by
    refine L.hasFDerivAt.comp_hasDerivAt 0 ?_
    have ht:= march b.val i.v 0
    rwa [starts] at ht
  have he : (fun t:ℝ=> L (drive b.val i.v t)) =ᶠ[𝓝 0] (fun _=>L i.v):= by
    filter_upwards [tepid H hd hG] with t ht
    change quoteL F _ _ _ = quoteL F _ _ _
    rw [ht.2 i,show films (1:Y) A=A from films_self A]
  rw [map_zero]
  exact (hp.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const ..)
end YM.RG11.Rigidity.Ice
