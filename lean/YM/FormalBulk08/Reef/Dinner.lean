import YM.FormalBulk08.Reef.Mantle

/-! Move the full exponent + measure across the repoking and gauge.
Result is an actual algebraic Elan (all g-orders with same `StepData` S).
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Wick Jets Orb Matrix Filter Set Precision Work.F05 RG Wilson Lattice Tree MeasureTheory Function PowerSeries
open Stationary hiding Rays
open YM.AnalyticNext.QuarticMatch.Joint hiding power
open scoped BigOperators ContDiff Topology Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {I : Type} [Fintype I]
variable (F : Forest S.ratio)
variable (T : Rays (Pine G S F⊕I)→ Rays (Pine G S F)) (u v : Rays I→Rays (wire G c))
    (hT : ContDiffAt ℝ ω T 0) (hu : ContDiffAt ℝ ω u 0) (hv : ContDiffAt ℝ ω v 0) (h0 : T 0=0) (u0:u 0=0) (v0:v 0=0)
def seat (W : Pap (wire G f)): Pap (Pine G S F⊕wire G c):= roam ℝ (motor (graft F)) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom W)
include hT hu h0 u0
lemma dessert (U : Pap (Glob G c f)) : dish (motor T) (motor u) (roam ℝ (motor (graft F)) U)=roam ℝ (motor (graft F ∘ hitch T u)) U := by
   rw [hull_dish T u (hu.of_le le_top) u0, roam_compose]
   have hh:= motor_compose (graft F (G:=G)) (hitch T u) ((graft_receipt F).of_le le_top) (hitch_smooth T u (hT.of_le le_top) (hu.of_le le_top)) (graft_origin F) (hitch_zero T u h0 u0)
   rw [show (fun i=>roam ℝ _ _) = _ from funext hh]
lemma drinking (W : Pap (wire G f)) : dish (motor T) (motor u) (seat F W)=roam ℝ (motor (offer G F ∘ T)) W := by
   rw [seat,dessert F T u hT hu h0 u0]
   unfold roam; rw [change_after,show (insertAt ℝ _).comp (MvPolynomial.rename Sum.inl).toRingHom=insertAt ℝ (motor (offer G F ∘ T)) from ?_]
   ext -- structural
   case hC _ _ _ => simp
   case hX i n m=> simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.rename_X,insert_X]; rfl
omit hT hu h0 u0

variable (s : Signed) (x : Site c) (k : Rays I→ Site c→G.El) (hk : Army k 0) (H : ∃ g:G.El,k 0=fun _=>g)
variable (B : ∀ᶠ z in 𝓝 0,input G c (v z)=Lattice.gauge (k z) (pull s x (input G c (u z))))
include hk H B hu hv u0 v0
lemma spicy (hp : S.patch.Branches S.kernel G) (t : S.Choices) :
   dish (still (Pine G S F) I) (motor u) (roam ℝ (motor (graft F)) (noisePin (G:=G) S t))= dish (motor (orbitY F s x k)) (motor v) (roam ℝ (motor (graft F)) (noisePin S t)) := by
    let T:=orbitY F s x k
    have ht:= snack F s x k hk H; have hq:= home_flat F s x k H
    let D:=fun z:Rays (Pine G S F⊕I)=> z ∘ Sum.inl
    have hd : ContDiffAt ℝ ω D 0:=contDiffAt_pi.mpr fun i=>contDiffAt_apply ..
    let Z:=graft F ∘ hitch D u; let R:=graft F ∘ hitch T v
    rw [still_on,dessert F D u hd hu rfl u0,dessert F T v ht hv hq v0]; change roam ℝ (motor Z) _= roam ℝ (motor R) _
    let t':=S.withinChoice s x t
    have he W (Q:Rays (Pine G S F⊕I)→ Rays (Glob G c f)): X^2*roam ℝ (motor Q) (noisePin S W)=roam ℝ (motor Q) (paste (clack S W)) := by rw [←salute S hp,roam,_root_.map_mul,map_pow,change_X]
    apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R:=_))); nth_rw 1 [clash S hp t t']
    have hZ : hitch D u 0=0:= hitch_zero _ _ rfl u0
    have hR : hitch T v 0=0:= hitch_zero _ _ hq v0
    have ha : ∀ (w:Rays (Pine G S F⊕I)→Rays (Pine G S F⊕wire G c)), ContDiffAt ℝ ∞ w 0 → w 0=0 → ContDiffAt ℝ ∞ (graft F ∘ w) 0:= by
        intro w ht hp; exact (show ContDiffAt ℝ ∞ _ _ from hp.symm ▸ (graft_receipt (G:=G) F).of_le le_top).comp 0 ht
    rw [he t' Z,he t R,←paste_steps (clack S t') Z ((discord _ hp _).of_le le_top) (ha _ (hitch_smooth _ _ (hd.of_le le_top) (hu.of_le le_top)) hZ) (by simp only [Z,Function.comp_apply,hZ,graft_origin]), ←paste_steps (clack S t) R ((discord _ hp _).of_le le_top) (ha _ (hitch_smooth T v (ht.of_le le_top) (hv.of_le le_top)) hR) (by simp only [R,Function.comp_apply,hR,graft_origin])]
    apply paste_replace
    have ht : Tendsto (fun i:Rays (Pine G S F⊕I)=> i ∘ Sum.inr) (𝓝 0) (𝓝 0) := tendsto_pi_nhds.mpr fun i=> (continuous_apply (Sum.inr i)).tendsto (0:Rays (Pine G S F⊕I))
    filter_upwards [ht.eventually B,swagger_cut F s x k hk H] with p he hp'
    change groupEnergy _ (S.prediction (input G f (offer G F (D p))) t') (input G c (u _))=groupEnergy _ (S.prediction (input G f (offer G F (orbitY F s x k p))) t) (input G c (v (p ∘ Sum.inr)))
    rw [hp',he,predicted hp,scheme_parent,uniform, S.prediction_channel hp s x, energy_channel]; rfl

omit B in
lemma healthy (U J : Pap (wire G f)) (E:Rite U J s (S.ratio.embed x)) :
   dish (still (Pine G S F) I) (motor u) (seat F U)=dish (motor (orbitY F s x k)) (motor v) (seat F J) := by
    let D:=fun z:Rays (Pine G S F⊕I)=> z ∘ Sum.inl
    have hd : ContDiffAt ℝ ω D 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    rw [still_on,drinking F D u hd hu rfl u0,drinking F (orbitY F s x k) v (snack F s x k hk H) hv (home_flat F s x k H) v0]
    apply E _ _ _ (scheme F s x k) (by rw [Function.comp_apply,show D 0=0 from rfl,map_zero]) (by rw [Function.comp_apply,home_flat F s x k H,map_zero]) ((offer G F).contDiff.contDiffAt.comp 0 hd) ((offer G F).contDiff.contDiffAt.comp 0 (snack F s x k hk H)) (skint F s x k hk) (equality_home F s x k H)
    exact swagger_cut F s x k hk H

lemma digestive (hp : S.patch.Branches S.kernel G) (P : ChartRatio G) (hr : LocalRatio P) (L : Hull (Pine G S F) (wire G c)) (t : S.Choices) (p : Pap (wire G f)) (hc : Civic p) :
   let Y:=orbitY F s x k
   ∃ M : Matrix (Pine G S F) (Pine G S F) ℝ,
      Elan L L (flush F t P p) (flush F t P p) (motor u) (motor v) (centered L L (motor Y) (motor u) (motor v)) (MvPolynomial.C.mapMatrix (dollars Y 0)) (MvPolynomial.C.mapMatrix M) := by
    intro Y;let f:=swivel F s x k
    have hT := snack F s x k hk H; have hX:=home_flat F s x k H
    obtain ⟨M,hm,hM⟩:= bread F P hr Y f (fun i=>feed_preserves ..) (fun i=>no_collapse ..) (swagger_fee F s x k hk H) (hT.of_le le_top) hX
    refine ⟨M,comparison L L _ _ _ _ _ _ _ hm (inlay Y) ?_⟩
    have hg:= healthy F u v hu hv u0 v0 s x k hk H p p (hc s _)
    have he:=caliber Y hX (hT.of_le le_top) M hm (sap F P) (sap F P) (sap_smooth F P hr) (sap_smooth F P hr) (sap_root F P hr) (sap_root F P hr) (motor u) (motor v) hM
    simp_rw [flush,vacuumU,_root_.map_sub,_root_.map_add,_root_.map_sub]; unfold seat at hg
    rw [he,hg,spicy F u v hu hv u0 v0 s x k hk H B hp]; change _ = _+covelog (gauche (motor (orbitY F s x k)) M); unfold Y; abel
end YM.FormalBulk08.Reef
