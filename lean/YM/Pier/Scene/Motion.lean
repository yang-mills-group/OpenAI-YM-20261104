import YM.Pier.Scene.Aspect
/-! Root chooses any present mark. For surviving surviving subsets after
removing constants, keep the Aspect bound as the global DIAMETER and
recenter on any remaining mark when using the multi-strobe producer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Panoramic
open Pier.Scene Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)

private lemma pullAccrue (u v : Site n) (U:Config G n): pull 1 v (pull 1 u U)=pull 1 (v+u) U := by
    rw [pull_one,pull_one,pull_one]; funext i; unfold Lattice.translate; rw [add_assoc]
-- no claim for integration across arbitrary retunings. AnchorC actual at grade d.
open GridApprox
set_option quotPrecheck false
include H in
private lemma oriented (u v:Site (C.side k p)) (a:ℕ) (y:C.label d) (ice:Bool)
    (he : k ≤ N) (hl : C.ref d ≤ k):
    writeF C y N k p a (v+u) he ice= (writeF C y N k p a v he ice) ∘
      pull 1 (GridApprox.anchor C.S p he u) := by
  let b:= betaDrop C d k N p a y v ice
  have hX : anchor C.S p he (v+u)=anchor C.S p he v +anchor C.S p he u:= (C.S.toDepth he p).root.map_add ..
  have hz : betaDrop C d k N p a y (v+u) ice = b ∘ pull 1 u:= by
     unfold b betaDrop; split
     · funext U; change -(alto C.path k d * Vitrines.enamel (C.localSection d) (C.path.rep N p k) (Spindle.parcel C d k N p y) a (pull 1 (v+u) U))= -(alto C.path k d * Vitrines.enamel (C.localSection d) (C.path.rep N p k) (Spindle.parcel C d k N p y) a (pull 1 v (pull 1 u U))); rw [pullAccrue]
     rfl
  have ha : u=anchor C.S p (le_refl k) u:= ((there u).symm.trans (vect C k p k u le_rfl))
  have hp:= backTo_orient C.path N p (h:=k) le_rfl he u (1:Signed)
    (show Envelope b from cylinder_env (dropped H v y hl he a ice))
  rw [← ha] at hp
  unfold writeF; rw [hX,hz,hp]; funext U
  change C.O N p y (anchor _ _ _ _ + _ ) U +_= C.O N p y (anchor _ _ _ _) (pull 1 _ U) + _
  apply congr_arg₂ (·+·); swap; · rfl
  rw [pull_one, C.translation]

omit [Fintype J] [DecidableEq J] in
lemma aspectTranslate {k p n wide:ℕ} (x:J→Site (C.side k p)) (i₀:J)
    (hd:∀ i j,separation (x i) (x j) ≤ wide*n)(hr:∀ i j,i≠j → n ≤ separation (x i) (x j)) :
    Nearest C k p n wide (fun i=> x i - x i₀) i₀ :=
    ⟨sub_self _,fun i=> by
         rw [← separation_translate (x i-x i₀) 0 (x i₀),sub_add_cancel,zero_add]; exact hd i i₀,
      fun i j he=> by simp_rw [sub_eq_add_neg, separation_translate]; exact hr i j he⟩

variable {φ:Filter I} {u ℓ:I→ℕ} {v s:I→ℝ}(L: GracesP C φ u ℓ)
    (T₀:Citizen C W r D)(wide:ℕ) (hbig:1≤wide)
local notation "B" i=> ((C.path.levels.budget (u i)).B)
include H T₀ hbig L
lemma neighbors (d:J→ℕ) (ice:J→Bool)(hz:∃ i,ice i=true) (hw:Coins φ (C.S.scale ∘ u) v)(hv:∀ᶠ i in φ,0<v i)(hs:Coins φ (C.S.scale ∘ u) s) (ht:∀ᶠ i in φ,0<s i) : ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), (∀ k j,separation (x k) (x j) ≤ wide*ℓ i) → (∀ k j,k≠j → ℓ i≤ separation (x k) (x j)) → ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ‖moment (C.beta N p) (fineJob (fun j=> writeF C (x₁ j) N (u i) p ((C.path.levels.budget (u i)).B) (x j) he.le (ice j)) univ)‖ ≤ s i:= by
   obtain ⟨i₀,h₀⟩:= hz
   obtain ⟨z,hz,hzm⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 (Fintype.card J))).exists
   filter_upwards [tinyJobs H L hbig ice i₀ hzm hz d T₀ i₀ h₀ hw hv hs ht,
     eventually_all.mpr fun j=> L.seeks.eventually_ge_atTop (C.ref (d j))] with i h hl N p he x hD hr x₁ hX
   let y j : Site (C.side (u i) p) := x j - x i₀
   have he' := h N p he y (aspectTranslate x i₀ hD hr) x₁ hX
   let f' (l:J) (x:Site (C.side (u i) p)):= writeF C (x₁ l) N (u i) p (B i) x he.le (ice l)
   let g:= fineJob (fun j=> f' j (y j)) univ
   let g₁:= pull 1 (GridApprox.anchor C.S p he.le (x i₀)) (K:=G.El)
   have hQ: fineJob (fun j=> f' j (x j)) univ=g ∘ g₁:= by
      have hP (j:J) : f' j (x j)=(f' j (y j)) ∘ g₁:= by
        nth_rw 1 [show x j=y j+x i₀ from (sub_add_cancel ..).symm]
        exact oriented H _ _ _ _ _ _ (hl j)
      unfold g fineJob; funext U; change _= ∏ j, f' j (y j) (g₁ U)
      exact Finset.prod_congr rfl fun i _ => congr_fun (hP i) U
   change ‖moment _ (fineJob (fun j=> f' j (x j)) _)‖ ≤ _; rw [hQ]
   have hF: Envelope g:= Envelope.prodC univ _ (fun j _=> write_e H (x₁ j) (B i) (y j) he.le (hl j) (ice j))
   exact (le_of_eq (congr_arg norm (moment_pull (C.beta N p) _ _ g (hF.integrableC _)))).trans he'
end YM.OPE.Strobe.Panoramic
