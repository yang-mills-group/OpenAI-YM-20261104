import YM.GradedFar.Physical.Appointment

/-!
# Exact cap filtration and orientation on these Fields; no arbitrary extra requirement
on the scale cocycle. Assert Tower obligations and price (proved on actual fields later).
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "V"=> U.sector.derivatives
local notation "S"=> U.room.kernel.spin
/-- Standard exact orientation properties. -/
structure oriented : Prop where
    raises (d e:ℕ)(h:d≤e) : ∀ᶠ r in τ,∀ x,J r e (up h x)=U.sector.derivatives.rise h (J r d x)
    unit (d:ℕ): ∀ᶠ r in τ,J r d (leaf G d)= P.unit d
    real (d:ℕ): ∀ᶠ r in τ,∀ x:Sec G d,J r d (Normalize.reel d x)= P.conj S d (J r d x)
    signed (d:ℕ): ∀ᶠ r in τ,∀ (s:Signed) (x:Sec G d), J r d (ori s.ortho d x)= P.mirror S d s (J r d x)
variable (hJ : oriented U J)
include hJ
set_option linter.unusedSectionVars false in
lemma handles' (d e:ℕ)(h:d≤e) {r u:ℝ}
    (hr : ∀ x, J r e (up h x)=U.sector.derivatives.rise h (J r d x))
    (hs : ∀ x, J (resize r u) e (up h x)=U.sector.derivatives.rise h (J (resize r u) d x)) (x : Sec G d) : next J e r u (up h x)= up h (next J d r u x) := by
  apply (J r e).injective
  change J r e ((J r e).symm _)= _; rw [LinearEquiv.apply_symm_apply,hr]; change J (resize r u) e _=_; rw [hs]; apply congr_arg; exact (LinearEquiv.apply_symm_apply ..).symm
lemma growth_fields (B : (d:ℕ)→ℝ→ Normalize.Change G d)
    (hK : ∀ d, ∀ᶠ r in τ, ∀ x, K r d x = J r d (stand (B d r) x))
    (hq : ∀ d, ∀ᶠ r in τ, ∀ x, stand (B (d+1) r) (up (Nat.le_succ d) x) = up (Nat.le_succ d) (stand (B d r) x)) : oriented U K where
  raises d e h := by
    have he (k:ℕ) (hp:d≤k) : ∀ᶠ r in τ, ∀ x, stand (B k r) (up hp x)=up hp (stand (B d r) x):= by
      induction k,hp using Nat.le_induction with
      | base=> exact Eventually.of_forall (fun r x=> rfl)
      | succ k hk ih=>
        filter_upwards [ih,hq k] with r hr hs
        intro x; change stand (B (k+1) r) (up (Nat.le_succ k) (up hk x)) = _; rw [hs,hr]; rfl
    filter_upwards [hK d,hK e,hJ.raises d e h, he e h] with r hi hj hr hx x
    rw [hi,hj,hx,hr]
  unit d := by filter_upwards [hK d,hJ.unit d] with r h he; rw [h,solitary,he]
  real d := by filter_upwards [hK d,hJ.real d] with r h he x; rw [h,h,← stood_reel,he]
  signed d := by filter_upwards [hK d,hJ.signed d] with r h he s x; rw [h,h,← stood_ori,he]
include H
lemma permissible_ready (d : ℕ) : ∀ᶠ r in τ,∀ z∈Growth.Small, permissible (Moving.forwards (next J d) r z) := by
    have up_scan : ∀ᶠ i : ℝ × ↥Growth.Small in filed, permissible (Moving.forwards (next J d) i.1 i.2.val) := by
       let f: Filter (ℝ × ↥Growth.Small) := filed; have ht:= (show Tendsto (Prod.fst : ℝ × ↥Growth.Small→ℝ) filed τ from tendsto_comap)
       have hs:= span_nears filed N M _ (fun i:ℝ × ↥Growth.Small=>i.2.val) ht (Eventually.of_forall (fun i=> i.2.property)) H
       have h : ∀ᶠ r in τ,∀ e:Fin (d+1),∀ x:Sec G e.val, J r d (up (Nat.le_of_lt_succ e.isLt) x)=
           U.sector.derivatives.rise (Nat.le_of_lt_succ e.isLt) (J r e.val x) := eventually_all.mpr (fun e=> hJ.raises _ _ _)
       filter_upwards [ ht.eventually (hJ.unit d), ht.eventually (hJ.real d), ht.eventually (hJ.signed d), ht.eventually h,
         hs.eventually (hJ.unit d), hs.eventually (hJ.real d), hs.eventually (hJ.signed d), hs.eventually h ] with i hU1 hR1 hT1 hr hU hR hT hq
       let r:=i.1; let z:=i.2.val; let s:= resize r z; let T:= next J d r z
       apply permissible.of_features
       · apply (J r d).injective; change J r d ((J r d).symm _) = _; exact ((J r d).apply_symm_apply _).trans (hU.trans hU1.symm)
       · intro j hj x hx
         let L: Sec G j:= ⟨x.val,hx⟩; rw [show x=up hj L from rfl]; have he:= handles' U J hJ j d hj (r:=r) (u:=z) (hr ⟨j,Nat.lt_succ_of_le hj⟩) (hq ⟨j,Nat.lt_succ_of_le hj⟩) L
         change (T _).val∈ _; rw [he]; exact (next J j r z L).property
       · intro x; apply (J r d).injective; change J r d ((J r d).symm _) = J _ _ (Normalize.reel d ((J _ _).symm _)); rw [LinearEquiv.apply_symm_apply,hR1,LinearEquiv.apply_symm_apply]; apply hR
       intro s x; apply (J r d).injective; change J r d ((J r d).symm _) = J _ _ (ori s.ortho d ((J _ _).symm _)); rw [LinearEquiv.apply_symm_apply,hT1,LinearEquiv.apply_symm_apply]; apply hT
    exact (eventually_comap.mp up_scan).mono fun r h z hz=> h (r,⟨z,hz⟩) rfl
end
end YM.FVA2.GradedFar.Physical
