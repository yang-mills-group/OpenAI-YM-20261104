import YM.FormalBulk08.Jets.Knit

/-! From local Haar-coordinate determinant identity to the exact formal Jacobian
factor, both relative to leading normalization. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick Orb Matrix PowerSeries Function Filter Set
open scoped BigOperators Classical Topology ContDiff
variable {V J : Type*} [Fintype V] [Fintype J]
omit [Fintype V] [Fintype J] in
lemma pose (y : V→ Pap (V⊕J)) (U : Pap V) : ∀ {I:Type*} (z : I→Pap J), dish y z (PowerSeries.map (MvPolynomial.rename (Sum.inl : V→ V⊕I)).toRingHom U) = roam ℝ y U := by
   intro I z
   unfold dish roam;rw [change_after,show (insertAt ℝ _).comp (MvPolynomial.rename (Sum.inl : V→ V⊕I)).toRingHom = insertAt ℝ y from (by ext <;> simp)]

def halo (ρ : Rays V→ℝ) (I : Type*) : Pap (V⊕I) := PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom (covelog (paste ρ))
omit [Fintype V] in
lemma veil (u v : PowerSeries (Glyphs ℝ V)) (hu : coeff 0 u=1) (hv : coeff 0 v=1) : covelog (u*v)=covelog u + covelog v := by
   have h : coeff 0 (u*v)=1 := by rw [coeff_zero_eq_constantCoeff_apply,map_mul,←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,hu,hv,mul_one]
   apply (expan_inj (covelog_rank h) (p:=covelog (u*v)) (q:=covelog u + covelog v) (by rw [map_add,covelog_rank hu,covelog_rank hv,zero_add])).mp; rw [expan_after h,←expan_mul (covelog_rank hu) (covelog_rank hv),expan_after hu,expan_after hv]

variable {I : Type*}
variable [DecidableEq V]
variable (F : Rays (V⊕J) → Rays V) (h : F 0=0) (H : ContDiffAt ℝ ∞ F 0) (M : Matrix V V ℝ) (hM : dollars F 0 * M=1)
include H in
lemma merch : ContDiffAt ℝ ∞ (fun p => (dollars F p).det) 0 := by
   simp_rw [Matrix.det_apply']; refine ContDiffAt.sum fun i _=> contDiffAt_const.mul ?h
   case h=>
     have he (x:V) := collar F H (i x) x
     convert! drawing (fun j:V=> fun p:Rays (V⊕J)=> dollars F p (i j) j) Finset.univ (fun i _=>he i) using 1; ext ;simp [Finset.prod_apply]
include h H hM
lemma caliber (p t : Rays V→ℝ) (hp : ContDiffAt ℝ ∞ p 0) (ht : ContDiffAt ℝ ∞ t 0) (h1 : p 0=1) (h2 : t 0=1)
    (z w : I→Pap J) (E : (fun x:Rays (V⊕J)=>p (x ∘ Sum.inl))=ᶠ[𝓝 0] fun x => (t (F x))*(M.det*(dollars F x).det)) :
   dish (still V J) z (halo p I)=dish (motor F) w (halo t I) + covelog (gauche (motor F) M) := by
    unfold halo; rw [pose,pose,still_on]
    have h0 : coeff 0 (paste p)=1 := by rw [paste_first,h1,map_one]
    have hg : coeff 0 (paste t)=1 := by rw [paste_first,h2,map_one]
    rw [show roam ℝ (motor F) (covelog (paste t))=covelog (roam ℝ (motor F) (paste t)) from change_covelog _ hg]
    let U:=fun x:Rays (V⊕J)=>x ∘ Sum.inl (β:=J)
    change roam ℝ (motor U) _= _
    rw [show roam ℝ (motor U) (covelog (paste p))=covelog (roam ℝ (motor U) (paste p)) from change_covelog _ h0]
    rw [←veil _ _ (rode (b:=motor F) hg) (gauche_unit (motor F) (dollars F 0) M (inlay F) hM)]
    have hD := merch F H
    congr 1
    let W:= fun x=> (dollars F x).det
    rw [←paste_steps _ U hp (contDiffAt_pi.mpr fun i=>contDiffAt_apply ..) rfl, ←paste_steps t F ht H h]
    unfold gauche; rw [rent F h H, ←paste_flat, ←paste_mul (fun _ : Rays (V⊕J)=> M.det) W contDiffAt_const hD, ←paste_mul (t∘F) ((fun _ : Rays (V⊕J)=>M.det)*W) ((h.symm ▸ ht : ContDiffAt ℝ ∞ t (F 0)).comp 0 H) (contDiffAt_const.mul hD)]; exact paste_replace E
end YM.FormalBulk08.Jets
