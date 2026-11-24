import YM.MSbar.Pole.Dimension.Iterating
import YM.MSbar.Pole.Dimension.Place

/-! # Continuation of one loop integration for smooth vertices

Kinematic form. Strip off the momentum measure factors (supplied in diagram
convention). `D` is the number of spacetime dimensions, complex, possibly
from an affine probe. `n` is NOT spacetime dimension; external momenta and
polarizations embedded in any `place n`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ambient
open Set Function Filter MeasureTheory place Radial
open scoped Topology InnerProductSpace ContDiff Classical BigOperators Real
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n:ℕ}

/-- Raw subintegral (normalized d-dimensional weight, `exp(-q²)` has mass one).
Strip Fourier and MS-bar scale factors; they will multiply once per free momentum. -/
def inside (n:ℕ) (K: ℝ×(place n × E) → ℂ) (x : E) (D : ℂ) :=
  ((π:ℂ)^n)⁻¹ * ∫ u:place n, dimensional K (u,x) (D-2*n)

abbrev Domain (n : ℕ) (U : Set E) := (Set.univ:Set (place n)) ×ˢ U
def screen (n:ℕ) (q:Price E) : Price (place n × E):= ticket (@Prod.fst (place n) E) * q.back Prod.snd

variable {K:ℝ × (place n × E) → ℂ} {p q : Price E} {U : Set E} {L : E→L[ℝ] ℂ} {b : ℂ}
private def tapMap (n:ℕ) (L : E→L[ℝ] ℂ) := L.comp (ContinuousLinearMap.snd ℝ (place n) E)
-- r will usually be inverse length; use D for actual dimension here.
theorem internal (o : IsOpen U) (hc : ContinuousOn p.val U) (hk : Packet (univ ×ˢ Domain n U)
    ((p.back (@Prod.snd (place n) E)).back Prod.snd) (Moment (screen n q)) K) (he : EvenOn (Domain n U) K)
    (R : ℝ) (hR : ∀ x∈U, ‖b+ L x‖ ≤ R) :
    (∀ x∈U, Integrable (fun u:place n => dimensional K (u,x) (b+L x-2*n))) ∧
    Packet U p q (fun x=> inside n K x (b+L x)) ∧
    (∀ v w : E, L w = Complex.I * L v →
      (∀ z∈univ ×ˢ Domain n U, CR ((0:ℝ),(0:place n),v) ((0:ℝ),(0:place n),w) K z) →
      ∀ x∈U, CR v w (fun x=>inside n K x (b+L x)) x) := by
  let T : place n × E → ℂ:= patch K (tapMap n L) (b-2*n)
  have hb (x:E) (u:place n) : T (u,x)=dimensional K (u,x) (b+L x-2*n) := by unfold T patch; congr 1; change b-2*n+L x=b+L x-2*n; abel
  obtain ⟨hp,H⟩:= finish (f:=K) (U:=Domain n U) (isOpen_univ.prod o) (hc.comp continuousOn_snd fun _ h=>h.2) hk he (tapMap n L) (b-2*n) (R+‖(2:ℂ)*n‖) (by
    rintro ⟨i,x⟩ hx; change ‖b-2*n+ L x‖ ≤ _; rw [sub_add_eq_add_sub]; exact (norm_sub_le ..).trans (add_le_add_left (hR _ hx.2) _))
  have ht : Barrel (volume:Measure (place n)) U p q (fun z x => T (z,x)) :=
    fullSlice (φ:=T) o hc (fun z=>z) (ticket (@id (place n))) (Eventually.of_forall fun z=>mem_univ z) hp
        (fun x hx => (continuous_iff_continuousAt.mpr (fun i => (hp.smooth (i,x) ⟨mem_univ _,hx⟩).continuousAt.comp
          (x:=i) (f:=fun u : place n=>(u,x)) (show Continuous (fun u:place n=>(u,x)) from by fun_prop).continuousAt)).aestronglyMeasurable)
        (volume:Measure (place n)).integrablePower toll
  have hv : (fun x=>inside n K x (b+L x))= fun x=>((π:ℂ)^n)⁻¹ * ∫ u:place n,T (u,x) := by funext x; simp_rw [inside,hb]
  rw [hv]; refine ⟨fun x hx => ?_,?_, fun v w hh hs x hx => ?_⟩
  · simp_rw [← hb]; exact ht.integrable hx
  · convert! ht.integrates.mul (Packet.const (((π:ℂ)^n)⁻¹)) using 1; funext; simp [mul_comm]
  have hx' : CR v w (fun x=>∫ u:place n,T (u,x)) x := by
    apply integral_cr ht hx
    filter_upwards with u; let P:=ContinuousLinearMap.inr ℝ (place n) E
    have hf : DifferentiableAt ℝ T (u,x):= (hp.smooth (u,x) ⟨mem_univ _,hx⟩).differentiableAt (by simp)
    have he' : HasFDerivAt (fun x:E=>(u,x)) P x:= (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id ..)
    exact CR.pull T he' hf (H (P v) (P w) hh hs _ ⟨mem_univ _,hx⟩)
  exact CR.mul (CR.hold _) hx' (differentiableAt_const _) (ht.exchange hx).differentiableAt

/-- Ordinary projection at physical dimension. -/
lemma phys (o : IsOpen U) (hc : ContinuousOn p.val U) (hk : Packet (univ ×ˢ Domain n U)
    ((p.back (@Prod.snd (place n) E)).back Prod.snd) (Moment (screen n q)) K) (he : EvenOn (Domain n U) K)
    {x:E} (hx : x ∈ U) : inside n K x ((2:ℂ)*n)=((π:ℂ)^n)⁻¹ * ∫ u:place n,K (0,u,x) := by
  unfold inside; rw [sub_self]; congr 1; refine integral_congr_ae (Eventually.of_forall fun i=>?_)
  exact ordinary (U:=Domain n U) (p:=p.back Prod.snd) (x:=(i,x)) (isOpen_univ.prod o) (hc.comp continuousOn_snd fun _ h=>h.2) hk he ⟨mem_univ i,hx⟩

end YM.MSbar.Pole.Ambient
