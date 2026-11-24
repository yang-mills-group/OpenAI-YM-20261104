import YM.Extra.MULTISOURCE_BOUNDS.Forest
import YM.LocalLTE.Concert.Contact
import YM.LocalLTE.Port.Moon
import YM.LocalLTE.Sapphire.Rose
/-! # Full E±K split of append book. Preserve probes, addresses, ownerships.
No volume costs in ports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} (P:Rep G n)
variable {V α :Type}[DecidableEq V]{R:Census V} (X:Layers P R α)
variable [Fintype α][Nonempty V]
local notation "C₀"=> X.Component
lemma chartBound {u k:ℝ}(h:Extra.Trajectories.Aperture P) (hp:P.activities.Valid P.p u k) (a d:α→ℝ)(hv:∀ i Z,‖X.residual i Z‖ ≤ a i) (hd:∀ i,0 ≤ d i) (hb:∀ i v, v∈ (X.tag i).val → P.p.supBounds (X.origins v) (X.region i) (X.H i) (d i)) (r: V→ℝ)(hw:∀ i,0<r i) (x y z w:ℝ)(hy: ∀ i,r i*‖X.units i‖ ≤ y)(hz:0<w) (hg:chargeFog P X k * chargeMark P X a r ≤ x*w) (he: ∀ v:V,SumBudget (fun i=>if v∈(X.tag i).val then Poly.toll r (X.tag i)*P.p.mass (X.region i) (d i) else 0) z): (X.bands).Radial r y z x w:=by
    obtain ⟨b,hb',hH⟩:=hp.boundK; have hf(i:ℕ):= (hb' i).2; let s':=X.bands; let M:= waft P X b a
    have h₃:= budget_loosen (brightBudget P X b a hf hv hH r hw) hg
    let k'(j:ℕ×ℕ):=if X.bands.entries j.1 j.2=0 then 0 else (unpin M 0 j.2)
    have hN(p:C₀):0 ≤ M p:=by
       apply prod_nonneg; rintro (i|i) _; exact (hb' i).1; exact (norm_nonneg _).trans (hv i 1)
    have h₁(j:ℕ×ℕ):0≤ k' j:=by
        unfold k'; split; rfl
        by_cases hu:j.2∈Set.range (pin:C₀→ℕ)
        · obtain ⟨p,hp⟩:=hu; rw [← hp,unpin_pin]; exact hN _
        rw [unpin_blank _ _ hu]
    let t:= unpin d 0; have h₂(j:ℕ):0 ≤ t j:=by
        by_cases h:j∈Set.range (pin:α→ ℕ); swap; ·exact (unpin_blank _ _ h).ge
        obtain ⟨p,rfl⟩:=h; unfold t; rw [unpin_pin]; exact hd _
    refine ⟨hw,hy,hz,⟨t,fun i=>⟨h₂ i,?_⟩,fun v=>?_⟩,k',fun i j=>⟨h₁ _,?_⟩,fun v=>?_⟩ -- Hits pair.
    · by_cases h:i∈Set.range (pin:α→ℕ)
      · obtain ⟨p,rfl⟩:=h; unfold t; simp only [bands,unpin_pin]; exact hb p
      intro i hi; unfold t; simp only [bands,unpin_blank X.H _ h,unpin_blank X.region _ h,unpin_blank d _ h]; exact Extra.Multi.supBounds_zero .. -- check
    · refine budget_image (pin_injective (α:=α)) injective_id ?_ ?_ (he v) ?_
      · intro i; split; exact mul_nonneg ((Poly.worth hw _).le) (mul_nonneg (Real.exp_nonneg _) (h₂ _)); rfl
      · intro i hi; split; next hv=> simp only [BudgetPoint.mass]; rw [show t i=0 from unpin_blank _ _ hi]; ring
        rfl
      intro i; simp only [bands,unpin_pin,id_eq]; split; next hl=> rw [show t (pin i)=d i from unpin_pin d 0 i] -- t shadow. edit
      next _=> rfl
    · intro Z; unfold k'; split; next h=> rw [h]; simp
      by_cases e:j∈ Set.range (pin:C₀→ℕ)
      · obtain ⟨c,rfl⟩:=e; simp only [bands,routed,unpin_pin]
        split
        next h=>
            unfold entry; split; next h'=> rw [norm_prod]; apply prod_le_prod (fun _ _=> norm_nonneg _); rintro (i|i) _; simpa only [Layers.weight,Sum.elim_inl,Complex.norm_real] using (hb' i).2 Z; exact hv i Z
            next _=> rw [norm_zero]; exact hN _
        simp only [Pi.zero_apply,norm_zero]; exact hN _
      simp only [bands,unpin_blank _ _ e,Pi.zero_apply,norm_zero,le_refl]
    let f (c:C₀):ℕ×ℕ:= (X.slot (.inr c),pin c); have hi:Injective f:= fun p q h=> pin_injective (congr_arg Prod.snd h); refine budget_image hi injective_id ?_ ?_ h₃ ?_
    · intro i; split; exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_nonneg _) (h₁ _)); rfl
    · intro i hi; split; next h'=>
          have hP:X.bands.entries i.1 i.2=0:=by
             by_cases hz:i.2∈Set.range (pin:C₀→ℕ); swap; · exact unpin_blank _ _ hz
             obtain ⟨c,hp⟩:=hz; simp only [← hp,bands,unpin_pin,routed]; exact if_neg fun h=>hi ⟨c,Prod.ext h hp⟩
          rw [show k' i=0 from if_pos hP]; ring_nf; simp [BudgetPoint.mass]
      rfl
    intro i; dsimp only [f,k']; split
    next ht=>
       simp only [bands,id_eq,unpin_pin, ← skin_slot X _ h]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)) (Poly.worth hw _).le
       split; exact hN _; rfl
    exact h₃.1 _
-- lift.Actual directly. `chartX`
lemma frosty {u k:ℝ}(h:HasSlots P.p P.activities)(hp:P.activities.Valid P.p u k)(a d:α→ℝ)(hv:∀ i Z,‖X.residual i Z‖ ≤ a i) (hd:∀ i,0 ≤ d i) (hb:∀ i v, v∈ (X.tag i).val → P.p.supBounds (X.origins v) (X.region i) (X.H i) (d i)) (r: V→ℝ)(hw:∀ i,0<r i) (x y z w:ℝ)(hy: ∀ i,r i*‖X.units i‖ ≤ y)(hz:0<w) (hg:chargeFog P X k * chargeMark P X a r ≤ x*w) (he: ∀ v:V,SumBudget (fun i=>if v∈(X.tag i).val then Poly.toll r (X.tag i)*P.p.mass (X.region i) (d i) else 0) z): (posta P R X).Radial r y z x w:= portedP _ _ _ (chartBound (glass P) (glace P R X) (gallery P h) (frosted P hp) a d hv hd hb r hw x y z w hy hz hg he)
end YM.LocalLTE.Port
