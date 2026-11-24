import YM.OPE.Compatible.Karls.Jay
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {P:ℕ→Mints E→L[ℝ] Mints E}{X:Mints E→L[ℝ] Mints E}
open Quit.PriceZ
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
variable {q y e z:ℝ}
namespace Eave
variable (K:Eave L X T a r q u k)
include K
lemma seaB :Bijective (cinT T X k):=by
     let C:=cinT T X k; constructor
     · exact (LinearMap.ker_eq_bot (f:=C.toLinearMap)).1 (LinearMap.ker_eq_bot'.mpr fun v hx=> Subtype.ext ((shineZ T K.HB K.mark K.chip s le_rfl _ v.property (fun i _=> congr_fun hx i)).limb))
     intro y; have he(i:ℕ)(h:i ≤ s):∃ p:Fruition X (μ k), ∀ j:Fin s, j.val < i → C p j=y j:=by  -- token `<i`
          induction i with
          | zero => exact ⟨0,fun _ _=>by omega⟩
          | succ i ih=>
              obtain ⟨t,ht⟩:= ih (by omega); let j:Fin s:=⟨i,h⟩; obtain ⟨g,hg⟩:= tintCan T K.HB K.mark K.chip j; let z:=y j-C t j; let u:Fruition X (μ k):=⟨g z,(hg z).1.1⟩; have hh: trims j.val u.val:=(hg z).1.2; refine ⟨t+u,fun l hl=>?_⟩; rw [map_add,Pi.add_apply]; by_cases hx:l=j; · subst l; rw [show C u j=z from (hg z).2]; unfold z; abel
              have hv:l.val < i:=Nat.lt_of_le_of_ne (show l.val ≤ i by omega) (fun H=> hx (Fin.ext H)); rw [show C u l= _ from (show _=_ from (show C u l= 0 from (show (T l).Tap k (u.val l)=0 from by rw [hh l hv,map_zero]))),add_zero]; exact ht _ hv
     obtain ⟨p,hp⟩:= he s le_rfl; exact ⟨p,funext fun i=>hp i i.isLt⟩
noncomputable def Vea : Fruition X (μ k)≃ₗ[ℝ](Fin s→ G k):= LinearEquiv.ofBijective (cinT T X k).toLinearMap K.seaB
lemma coal_sur (h:H): Surjective (K.PO h):=by
     intro p; let f:Unit→H:=fun _=>h; obtain ⟨x,hx,hF⟩:=(K.annex f).underW (show 0 ≤ (1:Unit→ℝ) from zero_le_one) (fun _=>p) ⟨‖p‖,norm_nonneg _,0,fun i=>by simp⟩; exact ⟨x (), (K.slotInv f () (x ())|>.trans (hF ()))⟩
-- maps temp strict
lemma Vita (k':ℕ)(hp:k'≤s){x:Fruition X (μ k)}:(∀ i:Fin s,i.val < k'→Vea K x i=0) ↔ trims k' x.val:= ⟨fun h=>shineZ T K.HB K.mark K.chip k' hp x.val x.property h,fun h i hi=>show (T i).Tap k (x.val i)=0 from by rw [h i hi,map_zero]⟩
end Eave
end YM.OPE.Hark
