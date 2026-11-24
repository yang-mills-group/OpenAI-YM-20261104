import YM.OPE.Compatible.Units

/-!
# Ordinary (single cluster) rate estimates, equivariant projection

At normalized log-length rates s>0 these include variable exterior
positions at rates with a strict gap. At s=0 give the line-rate zero cost
for compact-clearance exteriors (even noncompact if cleared). This includes
projection in this case; such a charge is useful when events at much
deeper scales absorb apparent growth here. They will be combined in
`Tree` with arbitrary horizons chosen internally for a *proof*, not a
changed projection convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (U : Spec.Final C f S)
variable {I J B l:Type} [Fintype I] [Fintype J] {φ : Filter l} {T : l → ℝ} {κ t b s c : ℝ}
  {X:l → I → E4} {Y:l → J → E4} {O:l → E4}
variable (H : Services C f S)
  [φ.NeBot] (hT : Tendsto T φ atTop)

include H hT
lemma step_rate (p : I → S.Tag) (hx : Kept φ T s X) (he : enveloped φ T s X O)
    (hs : 0 < s) (a : Tones U) : RateLE φ T (fun i=> lens U a (X i) p (O i))
      (((bill p:ℝ)-(a.fst:ℝ))*s) := by
  obtain ⟨P,hp⟩ := Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
  let n := a.fst
  let A := legends U
  let F := A.readIn n a
  let p' := Ward.expose ∘ p
  have hl := ray_v_shadow U H hp hT p hx he hs n
  have hq (g : Mode U.sector.derivatives) (hg : g∈ bands U.sector.derivatives n) :
      RateLE φ T (fun i => P.ope g (X i) p' (O i) • F (P.loaded g n))
       (((bill p:ℝ)-(n:ℝ))*s) := by
    have hw : g.fst ≤ n := (full_bands ..).mp hg
    by_cases hz : g.fst = n
    · exact ((available_cost U P p' hT H hp he hx hs g).smul (RateLE.const (F (P.loaded g n)) hT)).mono (by
        rw [hz,add_zero]; exact le_rfl)
    have hb : (facets U).part a.fst n (P.loaded g n) = 0 := by
      rw [P.cost _ hg,MultipleContact.Splitting.part_rise (facets U) U.room.kernel.laws.toSymmetric
        U.phase.transport.injection hw,MultipleContact.Splitting.beyondZero (facets U) (lt_of_le_of_ne hw hz),LinearMap.zero_apply]
    have hy : F (P.loaded g n) = 0 := Eq.trans (A.readIt n a _)
      ((congr_arg ((A.axisSet n).coord a.snd) (Subtype.ext hb)).trans (map_zero _))
    simp_rw [hy,smul_zero]
    exact RateLE.zero (X:=ℂ) _ _ _
  have hQ : RateLE φ T (fun i=> F (shadow P n (X i) p' (O i))) (((bill p:ℝ)-(n:ℝ))*s) := by
    unfold shadow; simp_rw [map_sum,map_smul]; exact RateLE.sum hT hq
  have hm := (hl.linear hT (LinearMap.toContinuousLinearMap (F.restrictScalars ℝ))).mono
    (show ((bill p:ℝ)-(n+1:ℝ))*s ≤ ((bill p:ℝ)-(n:ℝ))*s from mul_le_mul_of_nonneg_right (by linarith) hs.le)
  exact (hm.add hQ hT).congr (Eventually.of_forall fun i => by
    change F (ray U _ _ _ _ - shadow P n (X i) p' (O i)) + _ = _
    rw [map_sub,sub_add_cancel]; rfl)

lemma single_rate (p : I → S.Tag) (q : J → S.Tag) (r:l→Viewers U)
    (hx : Kept φ T s X) (hh : enveloped φ T s X O) (ht: Intervals φ T b (fun i=> sole (O i)) Y)
    (hs:b < s) (hb:0 ≤ b) (hy:Kept φ T t Y) (hg:b ≤ t) (n:ℕ) : RateLE φ T (fun i =>
      kernel (spectator U (r i)) (beside (X i) (Y i)) (beside p q) -
      Cov.insert S (spectator U (r i)) (O i) (Y i) q n (ray U n (X i) p (O i)))
       ((bill p:ℝ)*s-(n+1:ℝ)*(s-b)+(bill q:ℝ)*t) := by
  obtain ⟨P,hp⟩ := Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
  let v (i:l) := ray U n (X i) p (O i) - shadow P n (X i) (Ward.expose ∘ p) (O i)
  have hl := (count_insert U H hT n v q r ht hb hy hg
    (ray_v_shadow U H hp hT p hx hh (lt_of_le_of_lt hb hs) n)).mono
      (show ((bill p:ℝ)-(n+1:ℝ))*s+(n:ℝ)*b+(bill q:ℝ)*t ≤ ((bill p:ℝ)*s-(n+1:ℝ)*(s-b)+(bill q:ℝ)*t) by linarith only [hb])
  refine ((shadow_fit U H hp hT p q r hx hh ht hs hb hy hg n).sub hl hT).congr ?_
  filter_upwards with i; unfold v; rw [map_sub]; abel

-- zero-layer versions. Keep only fixed-clearance exteriors.
lemma clearance_rate (p : I → S.Tag) (q : J → S.Tag) (r:l→ Viewers U) (hx : Kept φ T 0 X)
    (he : Tendsto (fun i=> away (X i) (O i)) φ (𝓝 0)) (hy : ∀ᶠ i in φ, ClearOf (O i) (Y i) c)
    (hc : 0<c) : RateLE φ T (fun i=> kernel (spectator U (r i)) (beside (X i) (Y i)) (beside p q)) 0 := by
  obtain ⟨hh,h⟩ := free_clear hT hc hy
  have hη : 0 < c/2 := half_pos hc
  have hp : Intervals φ T 0 X Y := by
    intro b hb; filter_upwards [he.norm.eventually (gt_mem_nhds (show ‖(0:I→ E4)‖ < c/2 from by simpa using hη)), hy,
      ((RateIs.exp (-b) hT).tends (neg_lt_zero.mpr hb) hT).eventually (gt_mem_nhds hη)] with i hi hv hh j k
    have hκ : ‖X i j-O i‖ < c/2 := lt_of_le_of_lt (norm_le_pi_norm (away _ _) j) hi
    apply (show Real.exp (-b*T i) < c/2 from hh).trans_le
    linarith only [hv.openSpace k,c_dist_point (O i) (X i j) (Y i k),hκ,norm_sub_rev (X i j) (O i)]
  simpa only [mul_zero, add_zero] using (count_words U H hT p q r hx hh hp le_rfl le_rfl)

lemma ray_shallow (p : I → S.Tag) (hx : Kept φ T 0 X)
    (he : Tendsto (fun i=> away (X i) (O i)) φ (𝓝 0)) (n:ℕ) :
    RateLE φ T (fun i => ray U n (X i) p (O i)) 0 := by
  let Y : Empty → l → Unit → E4 := fun b => isEmptyElim b
  have hf := exchange U O X Y (fun _=>p) (fun b => isEmptyElim b) (fun b=> isEmptyElim b) hT he
    hx.inject (fun b => isEmptyElim b) (fun b => isEmptyElim b) (κ:=0)
    (fun K _ w y δ hδ h => by
      simpa only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,unselected_view] using
        (clearance_rate U H hT p w (fun _=>none) hx he h hδ)) n
  simpa only [Finset.univ_eq_empty,Finset.sum_empty,sub_zero] using hf

lemma single_shallow (p : I → S.Tag) (q : J → S.Tag) (r:l→Viewers U)
    (hx : Kept φ T 0 X) (he : Tendsto (fun i=> away (X i) (O i)) φ (𝓝 0))
    (hy : ∀ᶠ i in φ, ClearOf (O i) (Y i) c) (hc : 0<c) (n : ℕ) : RateLE φ T (fun i=>
      kernel (spectator U (r i)) (beside (X i) (Y i)) (beside p q) -
      Cov.insert S (spectator U (r i)) (O i) (Y i) q n (ray U n (X i) p (O i))) 0 := by
  obtain ⟨hw,h⟩ := free_clear hT hc hy
  apply (clearance_rate U H hT p q r hx he hy hc).sub (F':=fun i=> Cov.insert S (spectator U (r i)) (O i) (Y i) q n (ray U n (X i) p (O i))) _ hT
  simpa only [mul_zero, add_zero] using (count_insert U H hT n _ q r h le_rfl hw le_rfl (ray_shallow U H hT p hx he n))
end YM.OPE.Cov.Display
