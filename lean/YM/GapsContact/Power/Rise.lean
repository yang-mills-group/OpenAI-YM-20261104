import YM.GapsContact.Power.Sway
import YM.GapsContact.Slab.Dyadic
import YM.Push.FINITE_DETECTION.Test

/-!
# Weak horizon then prices for the whole Gram

Budgeting ANY real-scale leading pair uses rotations separately. Lower-sector contributions
must be separated at the *same* costs (and no contamination with unselected table tests of
another extraction!). Real Gram eliminates lower sectors and coarsens with a discount, then
yields sharp-power propagation (not claiming exact logarithms for fixed-reference labels).
-/

set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Metric Analysis Table Extraction Spec Ascent
open OPE.Levy Push.FiniteDetection Push.FiniteDetection.Free Trace.Terrace Trace.Pilot Climb Next.UVStress MergeProof.East Trace Trace.Over Ward
open scoped Topology BigOperators Classical NNReal InnerProductSpace ContDiff
variable {G:Gauge}{C: Family G} {d e n:ℕ}{r s:ℝ}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) {H:(Climb.Bel C.book).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Z:Trace.Terrace.Arch C}
variable (hG:G.Simple)(h : StarPath f H J F.room.kernel 𝓛) (Y:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "K" => C.labels
local notation "T" => Climb.Bel C.book
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "P" => Maxwell.Free.scheme C.labels
local notation "O" => Maxwell.Free.phase_orientation C.labels
local notation "I" => Maxwell.Free.scheme_filters C.labels
local notation "E" => (Climb.Bel C.book).Field
local notation "Q" => F.sector.derivatives
local notation "Hh" => F.room.kernel
local notation "iQ" => F.phase.transport.injection
local notation "oQ" => F.phase.transport.rights

include hG
lemma stronger (Y:Bliss F 𝓛 Z H)(d:ℕ):∀ᶠ r in trail, Good Hh d r := by
  obtain ⟨B,hB,hX⟩:= all_heights F hG Y d 1 1 one_pos
  exact hX.mono fun r hr=> hr.definitive

include h
omit hG
lemma free_check (x : E d) (y : E e) :
    Tendsto (fun k => knot S d (J.r k • detectors) (J.U k e y) (J.U k d x)) atTop (𝓝 (knot T d detectors y x)):=by
   let w := (![⟨d,x⟩,⟨e,y⟩] : Fin 2 → (T).Tag)
   let K' i := tested (J.r i) (isoPanel J i) w
   let L' := disc w
   simp_rw [knotted]; refine Metric.tendsto_nhds.mpr ?_; intro ε he
   let V:=fun i: Fin 2=> (w i).1
   let v: Ribbon T V:= fun i=> (w i).2
   filter_upwards [travels_jet F.room.kernel F.phase.transport.derivatives H₀ (Maxwell.Free.scheme_derives _) J h.approach (fun _ => v) v (fun _=> tendsto_const_nhds)
      0 {detectors} isCompact_singleton (singleton_subset_iff.mpr detectors_in) (ε/2) (half_pos he)] with i hi
   specialize hi detectors rfl; have h' : ![(⟨d,J.U i d x⟩:S.Tag),⟨e,J.U i e y⟩]=panels (isoPanel J i) ∘ w:= by funext j; fin_cases j<;> rfl
   rw [dist_eq_norm,h']; refine lt_of_le_of_lt ?_ (half_lt_self he)
   change ‖iteratedFDeriv ℝ 0 (K' i) _ - iteratedFDeriv ℝ 0 L' _‖ ≤ ε/2 at hi
   change ‖(K' i-L') detectors‖≤ ε/2
   rwa [show (iteratedFDeriv ℝ 0 (K' i) detectors - iteratedFDeriv ℝ 0 L' detectors)= iteratedFDeriv ℝ 0 (K' i-L') detectors by ext; simp, norm_iteratedFDeriv_zero] at hi

variable (hd:d≤e)

-- from both perspective; persistence of prices under graded restrictions of fields
lemma sponsor_rise (x:E d) : Tendsto (fun k=>(J.U k e).symm (F.sector.derivatives.rise hd (J.U k d x))) atTop (𝓝 ((P).rise hd x)):= by
   let β := Module.finBasis ℂ (E e)
   let b0 := freeMatrix (C:=C) β detectors
   let b (k : ℕ):= LinearMap.pi (fun i: Fin (Module.finrank ℂ (E e)) =>
    (knot S e (J.r k • detectors) (J.U k e (β i))).comp (J.U k e).toLinearMap)
   have hv : ∀ x i, b0 x i = knot (T) e detectors (β i) x := fun x i => (knot_val detectors x (β i)).symm
   apply Work.A04.tendsto_of_fitted b b0.toLinearMap (free_injective β)
   · intro x; refine tendsto_pi_nhds.mpr fun i => ?_; change Tendsto _ atTop (𝓝 (b0 x i)); rw [hv]; exact free_check F h x (β i)
   refine tendsto_pi_nhds.mpr fun i => ?_
   change Tendsto (fun k=> knot S e _ (J.U k e (β i)) (J.U k e ((J.U k e).symm _))) _ (𝓝 (b0 ((P).rise hd x) i))
   rw [hv,knot_lift P I hd _ detectors_in]; simp_rw [LinearEquiv.apply_symm_apply,knot_lift Q iQ hd _ (detector_in (J.positive _))]; exact free_check F h x (β i)

lemma boat_rise {A:Type*}{F':Filter A}{m:A→ℕ} (hm:Tendsto m F' atTop){x:A→E d}{v:E d}(hx:Tendsto x F' (𝓝 v)): Tendsto (fun i=>(J.U (m i) e).symm ((Q).rise hd (J.U (m i) d (x i)))) F' (𝓝 ((P).rise hd v)):=by
   let B (i:A): E d →ₗ[ℂ] E e:= (J.U (m i) e).symm.toLinearMap ∘ₗ ((Q).rise hd) ∘ₗ (J.U (m i) d).toLinearMap
   exact Dash.arcing (Dash.fit_plane B ((P).rise hd) (fun x=>(sponsor_rise F h hd x).comp hm)) hx

section
omit h
-- adapted Work.A04.tendsto_of_fitted to real CLMs on finite banks
lemma apprentices {M N A : Type*} [NormedAddCommGroup M][NormedAddCommGroup N][NormedSpace ℝ M][NormedSpace ℝ N][FiniteDimensional ℝ M][FiniteDimensional ℝ N] (L':Filter A) (f : A → M →ₗ[ℝ] N) (g : M →ₗ[ℝ] N)
    {w : A → M} {z : M} (hg : Injective g) (hf : ∀ x, Tendsto (fun k => f k x) L' (𝓝 (g x)))
    (hw : Tendsto (fun k => f k (w k)) L' (𝓝 (g z))) : Tendsto w L' (𝓝 z) := by
  obtain ⟨h, hh⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
  have he (x : M) : h (g x) = x := LinearMap.congr_fun hh x
  let B (k : A) : M →L[ℝ] M := LinearMap.toContinuousLinearMap (h.comp (f k))
  have hh' := h.continuous_of_finiteDimensional
  have ha : Tendsto B L' (𝓝 1) := by
    refine Trace.Terrace.fitV _ _ (fun x => ?_)
    change Tendsto _ _ (𝓝 x); nth_rw 2 [← he x]; exact (hh'.tendsto (g x)).comp (hf x)
  have hva : Tendsto (fun k => B k (w k)) L' (𝓝 z) := by rw [← he z]; exact (hh'.tendsto _).comp hw
  letI : CompleteSpace M:= FiniteDimensional.complete ℝ _
  have hi : Tendsto (fun k => Ring.inverse (B k)) L' (𝓝 (1 : M →L[ℝ] M)) := by
    rw [← Ring.inverse_one (M →L[ℝ] M)]
    exact (NormedRing.inverse_continuousAt (1 : (M →L[ℝ] M)ˣ)).tendsto.comp ha
  have hv := Trace.Terrace.beak _ _ _ _ hi hva
  rw [one_apply_eq_self] at hv
  apply hv.congr'
  filter_upwards [ha.eventually (Units.nhds (1 : (M →L[ℝ] M)ˣ))] with k hk
  change (Ring.inverse (B k) * B k) (w k) = _
  rw [Ring.inverse_mul_cancel _ hk]; rfl
end
variable {A:Type*}{l:Filter A}{m:A→ℕ} (hm:Tendsto m l atTop) {a:ℝ} (ha:0< a)

include hm ha hG
lemma chip_joint {x:A→E d}{v:E d}(hx:Tendsto x l (𝓝 v)) : Tendsto (fun i=>chip Hh d (J.r (m i)*a) (J.U (m i) d (x i))) l (𝓝 (chip H₀ d a v)) := by exact cost_seq F d hG h hm hx (s:=fun _=>a) tendsto_const_nhds ha

lemma bond_joint {x y:A→E d}{v w:E d}(hx:Tendsto x l (𝓝 v))(hy:Tendsto y l (𝓝 w)) : Tendsto (fun i=> bond Hh d (J.r (m i)*a) (J.U (m i) d (x i)) (J.U (m i) d (y i))) l (𝓝 (bond H₀ d a v w)) := by
   let a0(T' : Climb.Scaling S) (x y: A→ E d) i:= (bond Hh d (T'.r (m i)*a)) (T'.U (m i) d (x i)) (T'.U (m i) d (y i))
   let f(b:E d):=chip H₀ d a b
   have hs {L:Register G}{T0:Table L}(H : T0.Hierarchy) (x y:T0.Field d)(r)(hr:0<r): bond H d r x y= 2⁻¹*((chip H d r (x+y))^2 - (chip H d r x)^2 - (chip H d r y)^2):=by
      simp only [bond_root H hr, map_add, LinearMap.add_apply,bond_symm H hr y x]; ring
   rw [show bond H₀ d a v w = _ from hs (T0:=T) (H₀) v w a ha]; let V(i:A):=J.r (m i)*a
   apply ((((chip_joint F hG h hm ha (hx.add hy)).pow 2).sub ((chip_joint F hG h hm ha hx).pow 2)).sub ((chip_joint F hG h hm ha hy).pow 2)|>.const_mul (2:ℝ)⁻¹).congr
   intro i; rw [hs Hh _ _ _ (mul_pos (J.positive _) ha)]; simp only [map_add]

include Y
local instance (e : ℕ) : FiniteDimensional ℝ (E e) := Module.Finite.trans ℂ _

omit h hG Y in
lemma secular : Tendsto (fun i=>J.r (m i)*a) l trail:= tendsto_nhdsWithin_iff.mpr ⟨by simpa using (J.drips.comp hm).mul_const a,Eventually.of_forall fun i=> mul_pos (J.positive _) ha⟩

lemma nearby_edge {X:A→ E (d+1)}{x₀:E (d+1)} (hX:Tendsto X l (𝓝 x₀)) : Tendsto (fun i=>(J.U (m i) d).symm (edge Hh Q d (J.r (m i)*a) ((J.U (m i)) (d+1) (X i)))) l (𝓝 (edge H₀ P d a x₀)) := by
   let e := d+1
   let v' (i:A) (d:ℕ):= ((J.U (m i) d).toLinearMap.restrictScalars ℝ)
   let D:= Fin (Module.finrank ℝ (E d))
   let β := Module.finBasis ℝ (E d)
   let g : E d →ₗ[ℝ] D → ℝ:= LinearMap.pi fun j=> (bond H₀ d a).flip (β j)
   let f (i:A): E d →ₗ[ℝ] D→ℝ:= LinearMap.pi fun j=> ((bond Hh d (J.r (m i)*a)).flip (v' i d (β j))).comp (v' i d)
   refine apprentices l f g ?_ (fun x=> tendsto_pi_nhds.mpr fun j=> bond_joint F hG h hm ha (x:=fun _=> x) tendsto_const_nhds (y:=fun _=> β j) tendsto_const_nhds) ?_
   · intro x y ht; apply (bankable H₀ ha (good_blue C d ha)).1; exact β.ext fun i=> congr_fun ht i
   refine tendsto_pi_nhds.mpr fun j=>?_;
   let U i:= Up (Q) d (J.U (m i) d (β j)); let z i:=(J.U (m i) (d+1)).symm (U i)
   have hz : Tendsto z l (𝓝 (Rise0 C d (β j))):=(sponsor_rise F h (Nat.le_succ d) (β j)).comp hm
   change Tendsto _ l (𝓝 (bond H₀ d a (edge H₀ P d a x₀) (β j))); rw [edger H₀ P ha (good_blue C d ha)]; apply (bond_joint F hG h hm ha hX hz).congr'
   filter_upwards [(secular (J:=J) hm ha).eventually (stronger F hG Y d)] with i hi
   change bond Hh (d+1) (J.r (m i)*a) (J.U (m i) (d+1) (X i)) ((J.U (m i)) (d+1) ((J.U (m i) (d+1)).symm (U i))) = bond Hh _ _ (J.U (m i) d ((J.U (m i) d).symm _)) _; simp only [LinearEquiv.apply_symm_apply]; rw [edger Hh Q (mul_pos (J.positive _) ha) hi]; rfl

lemma nearby_ridge {X:A→ E (d+1)}{x₀:E (d+1)} (hX:Tendsto X l (𝓝 x₀)) : Tendsto (fun i=>(J.U (m i) (d+1)).symm (ridge Hh Q d (J.r (m i)*a) ((J.U (m i)) (d+1) (X i)))) l (𝓝 (ridge H₀ P d a x₀)):=by
   simp_rw [ridged,map_sub,LinearEquiv.symm_apply_apply]
   refine Tendsto.congr ?_ (hX.sub (boat_rise F h (Nat.le_succ d) hm (nearby_edge F hG h Y hm ha hX))) -- argument order
   intro i; rw [LinearEquiv.apply_symm_apply]
lemma nearby_sip {X:A→ E (d+1)}{x₀:E (d+1)} (hX:Tendsto X l (𝓝 x₀)) : Tendsto (fun i=>sip Hh Q d (J.r (m i)*a) ((J.U (m i)) (d+1) (X i))) l (𝓝 (sip H₀ P d a x₀)):= by
   apply (chip_joint F hG h hm ha (nearby_ridge F hG h Y hm ha hX)).congr; intro i; rw[LinearEquiv.apply_symm_apply]; rfl
end YM.GapsContact.Power
