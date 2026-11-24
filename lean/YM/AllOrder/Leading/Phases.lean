import YM.AllOrder.Leading.Plate

/-!
# The bounds on compact separated physical shapes and smooth test profiles

Will use to call `PositionX` scheme's normalization/profile interface;
operator-product queries can use `Plate.scalar_flat` and `Plate.remainder`
(with macroscopic spectators). These suffice in particular for matching the
identity channel given a formal match on unselected correlations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Next.UVStress Maxwell OPE OPE.Orbits FrameCost OPE.Nesting MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {n : ℕ} {d : Caps n} {K : Set (Points n)}

-- adapt `Coverage/Diagonal` private equalities to any appropriate phase table
lemma moment_fin {G : Gauge}{L : Register G}{n : ℕ}(S T:Table L) (z:Points n)(d:Caps n) (v:Ribbon S d)
    (h:T.Hierarchy)(hz:z∈conf n):
    S.classMoment T d z v = moment T z.ofLp v := by
    let f:=finCongr (Fintype.card_fin n)
    let g:= (runNames (Fin n)).symm.trans f
    have he:= permuted (T:=T) (a:=v) (y:=z.ofLp) h hz g
    rw [← he]; let t:= hang d v
    have ht (m : ℕ) (h:m=n): S.classMoment T d z v = S.useAt T
       (points fun i:Fin m=> z.ofLp (Fin.cast h i)) (t ∘ Fin.cast h) := by subst m;rfl
    refine Eq.trans (ht _ (Fintype.card_fin n)) (congr_arg₂ (S.useAt T) (congr_arg points (funext fun i=>?_)) (funext fun i=>?_))
    · change z (f i)= z (g (runNames _ i)); rw [show (g (runNames _ i)) = f i from by simp [g,f]]
    change t (f i) = t (g (runNames (Fin n) i))
    rw [show (g (runNames _ i)) = f i from by simp [g,f]]

lemma fits_plate {x : Points n} {M : ℝ} (h:x∈Scaling.window M n) : x.ofLp∈ Short.plate (Fin n) M M⁻¹ := by
    refine ⟨fun j => ?_,fun j k he=> ?_⟩
    · simp only [sub_zero,mul_one]; exact (PiLp.norm_apply_le x j).trans h.2
    rw [mul_one]; refine (h.1 j k he).trans ?_; unfold cubedist; rw [dist_eq_norm]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => PiLp.norm_apply_le (x j-x k) a

variable (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (v : Ribbon (Bel C.book) d)
variable (h : Aligned F g U) (hF : Services C f S) (hG : G.Simple)

def phaseRead (F : Spec.Final C f S) (U : ℝ → FamilyFrame S) (v : Ribbon (Bel C.book) d)
    (r : ℝ) (q : Viewers F) (x : Points n) := S.classMoment (spectator F q) d (r • x) (placed U v r)
lemma phase_zero (r : ℝ) (hr : 0<r) (q : Viewers F) {x : Points n}(hx:x∈conf n):
    phaseRead F U v r q x= moments F U v r x.ofLp 0 q := by
    have he : (r • x).ofLp=Short.harmonic r x.ofLp 0 := funext fun i=>(add_zero (r • x i)).symm
    rw [phaseRead, Leading.moments,moment_fin S (spectator F q) _ _ _ (spectate F q) ((enlarged hr x).1 hx),he]
lemma phase_continuous (r : ℝ) (hr : 0<r) (q : Viewers F) : ContinuousOn (phaseRead F U v r q) (conf n) :=
    (S.class_smooth _ (spectate F q).smooth (hang d (placed U v r))).continuousOn.comp (g:=fun x=> S.useAt (spectator F q) x (hang d (placed U v r))) (f:=fun x => r • x)
      (ContinuousOn.const_smul continuousOn_id r) (fun x hx => (enlarged hr x).1 hx)

include h hF hG R
lemma phase_leading (hK : IsCompact K) (hV : K ⊆ conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in trail, ∀ x∈K, ∀ q : Viewers F,
       ‖phaseRead F U v r q x-disc (hang d v) x‖ < ε := by
    obtain ⟨M,hM,hP⟩ := ((Work.A05.compact_fits hK hV).and (eventually_gt_atTop (0:ℝ))).exists
    filter_upwards [plate (M:=M) R v h hF hG (inv_pos.mpr hP) he,
       show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin] with r hr hm x hx q
    have hu : disc (hang d v) x= Levy.freeSlots (C:=C) v x.ofLp :=
       moment_fin (Bel C.book) _ _ _ _ (Free.hierarchy C.labels) (hV hx)
    rw [hu,phase_zero v r hm q (hV hx)]; exact (hr _ (fits_plate (hM hx)) 0 q).1
lemma phase_flat (hK : IsCompact K) (hV : K ⊆ conf n) {δ : ℝ} (hd : -1<δ) :
    ∀ᶠ r in trail, ∀ x∈K, ∀ q : Viewers F,
       ‖phaseRead F U v r q x-tableRead (U r) r (hang d v) x‖ ≤ 2*Real.exp (δ * FrameCost.clock r) := by
    obtain ⟨M,hM,hP⟩ := ((Work.A05.compact_fits hK hV).and (eventually_gt_atTop (0:ℝ))).exists
    filter_upwards [scalar_flat (M:=M) R v h hF hG (inv_pos.mpr hP) δ hd,
       show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin] with r hr hm x hx q
    change ‖phaseRead F U v r q x-phaseRead F U v r none x‖≤_
    simp_rw [phase_zero v r hm _ (hV hx)]
    apply (norm_sub_le_norm_sub_add_norm_sub _ (scalarChannel F R U v r x.ofLp 0) _).trans
    rw [norm_sub_rev (scalarChannel ..) _, two_mul]; exact add_le_add (hr _ (fits_plate (hM hx)) 0 q) (hr _ (fits_plate (hM hx)) 0 none)

-- retain the actual fixed test norm/profile cost needed when varying within the compact
omit h R hF hG in
lemma general_profile (u : Test n) {A : ℝ} {x y : Points n → ℂ}
    (hx : ContinuousOn x (conf n))(hy : ContinuousOn y (conf n))
    (h : ∀ s ∈ tsupport u, ‖x s-y s‖ ≤ A) :
    ‖u.applyTo x-u.applyTo y‖ ≤ (∫ i, ‖u i‖) * A := by
    have hi : Integrable (fun i => ‖u i‖) := (u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport).norm
    rw [← Next.UVStress.test_sub _ _ hx hy]
    have hv : ∀ i, ‖u i*(x i-y i)‖ ≤ ‖u i‖* A := fun i=> by
        by_cases hf : i∈tsupport u
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h i hf) (norm_nonneg _)
        simp [image_eq_zero_of_notMem_tsupport hf]
    have ht:= (norm_integral_le_integral_norm (fun i=>u i*(x-y) i)).trans
       (integral_mono (u.smearing (hx.sub hy) |>.norm) (hi.mul_const A) hv)
    rwa [integral_mul_const] at ht
lemma all_tests (hK : IsCompact K) (hV : K ⊆ conf n) {ε δ : ℝ} (he : 0<ε)(hd : -1<δ) :
    ∀ᶠ r in trail,∀ q : Viewers F,∀ u : Test n,tsupport u ⊆ K →
       ‖u.applyTo (phaseRead F U v r q)-u.applyTo (disc (hang d v))‖ ≤ (∫ x, ‖u x‖)*ε ∧
       ‖u.applyTo (phaseRead F U v r q)-u.applyTo (tableRead (U r) r (hang d v))‖ ≤ (∫ x, ‖u x‖)*(2*Real.exp (δ*FrameCost.clock r)) := by
    filter_upwards [phase_leading R v h hF hG hK hV he,phase_flat R v h hF hG hK hV hd,
       show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin] with r hR hB hr q u hu
    exact ⟨general_profile u (phase_continuous v r hr q) (smoothDisc (Free.hierarchy C.labels).smooth _).continuousOn
       (fun x hx=>(hR x (hu hx) q).le),general_profile u (phase_continuous v r hr q) (phase_continuous (F:=F) v r hr none) (fun x hx=>hB x (hu hx) q)⟩
lemma test_tend (u : Test n) (q : ℝ → Viewers F) : Tendsto (fun r => u.applyTo (phaseRead F U v r (q r))) trail
     (𝓝 (u.applyTo (disc (hang d v)))) := by
    apply profile_limit u ((show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin).mono fun r hr=> phase_continuous v r hr (q r))
       (smoothDisc (Free.hierarchy C.labels).smooth _).continuousOn
    intro ε he; exact (phase_leading R v h hF hG u.hasCompactSupport u.tsupport_subset he).mono
       fun r hr x hx=>(hr x hx (q r)).le
end YM.AllOrder.Leading
