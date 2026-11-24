import YM.OPE.Compatible.Frog.Eye
/-!
# suspension equiv.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{x:ℝ}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
abbrev rare (i:Phase)(A:Tracts G d τ):=∀ j < i,A j=0
variable (G)(h:Aware d τ)
local notation "Q!"=> solar G d τ
local notation "M!"=> Tracts G d τ
local notation "W!"=> relief G h
include h
lemma honors (x:M!)(i:Phase)(hp:rare i x): (W! x).val i=(x i).val:=by
     let U:= ContinuousLinearMap.proj (R:=ℝ) i ∘L (Q!).subtypeL; rw [show (W! x).val i=U (W! x) from rfl]; unfold relief; rw [_root_.sum_apply,map_sum,sum_eq_single i]; exact (crestP G h i (x i)).1
     · intro j _ hj; rcases lt_or_gt_of_ne hj with hh|hh
       · change U (crestL G h j (x j))= _; rw [hp j hh,map_zero,map_zero]
       exact (crestP G h j (x j)).2 i hh
     simp
lemma scaleFil (x:M!)(i:Phase): rare i x↔ ∀ j < i,(W! x).val j=0:=by
     constructor;· intro h j hj; rw [honors G ‹_› x j (fun i hi=>h i (hi.trans hj)),h _ hj];rfl
     intro hx; let f(k:ℕ):=∀ j:Phase,j.val=k→ j < i→ x j=0; have he(k:ℕ): f k:=by
          induction k using Nat.strong_induction_on with | h k ih=>
             intro j hj hy; let V:= x j; apply Subtype.ext; exact show V.val=0 from ((honors G h x j (fun u hp=> ih u.val (hj ▸ Fin.lt_def.mp hp) u rfl (hp.trans hy))).symm.trans (hx _ hy))
     exact fun j hg=> he j.val j rfl hg
lemma singular (x:Phase)(p: bed G (d+x.val) (τ x)): W! (Pi.single x p) = crestL G h x p:=by
     unfold relief; rw [_root_.sum_apply,sum_eq_single x]; simp; intro i _ hx; simp [Pi.single_eq_of_ne hx]; simp
lemma hoof : Bijective W!:=by
      constructor
      · apply (LinearMap.ker_eq_bot (f:=(W!).toLinearMap)).mp (LinearMap.ker_eq_bot'.mpr fun x hx=>?_); ext1 i; apply Subtype.ext; have ht : W! x=0:=hx; exact (honors G h x i ((scaleFil G h x i).mpr (fun j hj=>by rw [ht];rfl))).symm.trans (by rw [ht];rfl)
      intro x
      have he(n:ℕ): ∃ u:M!,∀ j: Phase,j.val<n→ (W! u).val j=x.val j:=by
           induction n with
           | zero=> exact ⟨0,fun j h=>by omega⟩
           | succ n ih=>
                obtain ⟨p,hp⟩:=ih; by_cases hh:n<3; swap; · exact ⟨p,fun j _=>hp j (by have h:=j.isLt;omega)⟩
                let y:Phase:=⟨n,hh⟩; let z:=x-W! p; have hz:∀ j<y,z.val j=0:=fun j hj=>sub_eq_zero.mpr (hp j hj).symm; let w: bed G (d+y.val) (τ y):=⟨z.val y,oak z.val z.property y hz⟩
                refine ⟨p+Pi.single y w,fun j hj=>?_⟩; rw [map_add,singular]; by_cases he:j=y
                · subst j; change (W! p).val y+ (crestL G h y w).val y=_; rw [(crestP G h y w).1,show w.val=x.val y-(W! p).val y from rfl]; abel
                have hl:j<y:=Fin.lt_def.mpr (lt_of_le_of_ne (show j.val≤n from by omega) (fun H=> he (Fin.ext H))); change (W! p).val j+ _ =_; rw [show _= _ from (crestP G h y w).2 j hl,add_zero]; exact hp _ hl
      obtain ⟨p,hp⟩:=he 3; exact ⟨p,Subtype.ext (funext fun i=> hp _ i.isLt)⟩
noncomputable def PoseQ (G:Gauge)(h:Aware d τ): Tracts G d τ≃L[ℝ] solar G d τ := ContinuousLinearEquiv.ofBijective (relief G h) (LinearMap.ker_eq_bot.mpr (hoof G h).1) (LinearMap.range_eq_top.mpr (hoof G h).2) -- name
end YM.OPE.Drift
