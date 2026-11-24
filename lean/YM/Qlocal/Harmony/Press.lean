import YM.Qlocal.Harmony.Focal
import YM.Qlocal.Harmony.Woof
/-!
# Summable superpositions in Fk

Work with finite-dimensional **actual tangent** jets on the current finite regulator. Winding
costs and uniformity in regulator mass don't follow from this lemma. It is for commuting the
conditional/vacuum/root normalizations with sums of kernel data (keeping them fixed except for a
disjoint finite collection of nonempty marked drivers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Function Finset Filter Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Bulk Dialect Reckoner
open Matrix Push Uniform SectorMeasure PhysicalNext Next.Fluctuations Next.SectorChange Multi PertExtension.Series
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
namespace Focal
variable {V J:Type} [DecidableEq V] [DecidableEq J] [Fintype V] [Fintype J] {R:Census V}
    {α:J→Type*} {G: Gauge} {c f:Side} {π:Clip} {O:ChartRatio G} {P:PathData G} {S:StepData c f}
variable (K:Bulk.Kernel S π P O) (H:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c 1)
    (δ:J→Multi.Hot R) (s:R.Mode) (χ: Bulk.Colors R G f)
set_option quotPrecheck false
local notation "X'"=> Bulk.Joint S H (G:=G)
local notation "Ω"=> Driver G H
abbrev CML (X Y:Type)[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y] (n:ℕ):=
  ContinuousMultilinearMap ℝ (fun _:Fin n=> X) Y
-- for both real & complex. Similar to Formal.Canvas. Avoid global instance.
scoped instance limited {X Y:Type}[NormedAddCommGroup X][NormedAddCommGroup Y]
   [NormedSpace ℝ X][NormedSpace ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
   (n:ℕ): FiniteDimensional ℝ (CML X Y n):= by
 let T : CML X Y n →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n=> X) Y := {
   toFun := fun x=> x.toMultilinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl}
 exact FiniteDimensional.of_injective T ContinuousMultilinearMap.toMultilinearMap_injective

local notation "P[" n "]"=> CML (Bulk.Joint S H (G:=G)) ℂ n
-- account height `n` may include `χ.power`, which is fixed (not selected per Sail)
noncomputable def coupons (G:Gauge) (H: Forest S.ratio)(k n:ℕ) : Driver G H →ₗ[ℝ]∀ j:Fin (n+1), CML (Bulk.Joint S H (G:=G)) ℂ (k+j.val) where
  toFun p j:= iteratedFDeriv ℝ (k+j.val) (Bulk.posed S H p.val) 0
  map_add' p q:= by
    funext i; exact iteratedFDeriv_add_apply ((smooth_iff H _|>.1 p.prop).of_le le_top) ((smooth_iff H _|>.1 q.prop).of_le le_top)
  map_smul' c p:= by
    funext i
    change iteratedFDeriv ℝ (k+i.val) (c • (Bulk.posed S H p.val)) 0=c • _
    exact iteratedFDeriv_const_smul_apply ((smooth_iff H _|>.1 p.prop).of_le le_top)

lemma compose_poses {T: Poly R→ₐ[ℂ] Poly R}(he:T=AlgHom.id ℂ (Poly R))(r:ℕ)(u : Order.Grade R r) : Dialect.Keeper.morph T (Order.indices r) u=u:= by
 subst T; exact Keeper.sheet_ext R (fun i=>Keeper.morph_sheet (AlgHom.id ℂ _) i u)

variable (Y Z:J→Driver G H)
    (hδ:Exhibit.relevant δ s (Planet.pack univ))
    {r i:ℕ}(hr:i≤r)
local notation "κ"=> χ.power ∘ δ
local notation "Ω'"=> Driver G H
-- extensional equality only requires a finite-dimensional jet. normalize to gauge.
include hδ
omit [Fintype V] in
lemma mark_same
    (hq:∀ j,coupons G H ((κ) j) r (Y j)=coupons G H ((κ) j) r (Z j))
    (A: X') (a:Multi.Hot R) {k:ℕ}(ha:k≤r):
    Assembly.markLetter χ.power (markFn S H (sheet H δ χ Y 1)) a A k= Assembly.markLetter χ.power (markFn S H (sheet H δ χ Z 1)) a A k:=by
 let E (Q':J→Driver G H):ℝ→ Config G f→ℂ:= room H δ Q' 1 a
 let L (g:ℝ→ Config G f→ℂ):= iteratedFDeriv ℝ (χ.power a+k) (Bulk.posed S H g) 0
 change _ • L (room H δ Y 1 a) _ = _ • L (room H δ Z 1 a) _
 congr 2
 clear E
 unfold L
 by_cases hn:a∈Set.range δ; · obtain ⟨j,rfl⟩:=hn; rw [room_here H δ _ (unique_shape δ s hδ),room_here H δ _ (unique_shape δ s hδ),Pi.one_apply,one_smul,one_smul]; exact congr_fun (hq j) (⟨k,Nat.lt_succ_of_le ha⟩:Fin (r+1))
 rw [room_blank H δ _ _ _ hn,room_blank H δ _ _ _ hn]
lemma publish_eq (hq:∀ j,coupons G H ((κ) j) r (Y j)=coupons G H ((κ) j) r (Z j)): publish K H t x δ s χ Y 1 r i=publish K H t x δ s χ Z 1 r i:= by
 unfold publish Symmetry.Orbit.words; let T:=AlgHom.id ℂ (Poly R); have hx:Fk K H t (sheet H δ χ Y 1) x r=Fk K H t (sheet H δ χ Z 1) x r:=by
    refine Eq.trans (compose_poses (T:=T) rfl r _).symm (Keeper.Fk_natural T (fun _=>rfl) K H t x _ _ rfl ?_)
    intro p i hi; exact congr_arg (Multi.lit R) (funext fun j: Multi.Hot R=>mark_same H δ s χ Y Z hδ hq p j hi)
 rw [hx]

include hr
open scoped YM.Qlocal.Harmony.Focal
-- intertwining oracle costs only. No newly postulated convergence of Fk on analytic-coupling
-- functions; this is for one coefficient and one finite regulator (tensors over the entire test
-- horizon & true Gaussian covariance, not replacing actual by an alternative vacuum).
set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 300000 in
lemma pose_book (a:∀ i,α i→ℝ) (T:∀ i, α i → Driver G H)
    (h:∀ j (l:Fin (r+1)), HasSum (fun i=>a j i • ((coupons G H ((κ) j) r (T j i)) l)) ((coupons G H ((κ) j) r (Y j)) l)):
    HasSum (fun z:∀ i,α i=> (∏ i:J,a i (z i)) • publish K H t x δ s χ (fun i=> T i (z i)) 1 r i) (publish K H t x δ s χ Y 1 r i):=by
 let F (j:J):= coupons G H ((κ) j) r
 refine distribute (gesture K H t x δ s χ hδ hr) T (E:=fun j=>(l:Fin (r+1)) → CML (Bulk.Joint S H (G:=G)) ℂ ((κ) j+l.val)) F (fun Y Z ht=>publish_eq K H t x δ s χ Y Z hδ ht) a Y ?_
 intro j; apply tendsto_pi_nhds.mpr; intro q; exact (h j q).congr (fun _=> by rw [Finset.sum_apply]; rfl)

end Focal
end YM.Qlocal.Harmony
