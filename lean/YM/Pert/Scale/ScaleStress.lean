import YM.Pert.Scale.MovingFunctional
import YM.Pert.Scale.Attached
/-!
Reading back the **physical** Final-sector stress in the same original X field coordinates. Mixed-field data from FirstExtension plus separated, reflected free fullness suffice; no normalization by declaration.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Pert.Scale
open Extra.FD Maxwell RawLabels Position Spec Climb Set Function Filter Topology Analysis Ward Table Next.UVStress
open scoped Topology ContDiff ComplexOrder

private def two {V : Type} [AddCommGroup V] [Module ℂ V] (L : MultilinearMap ℂ (fun _ : Fin 2 => V) ℂ) (q : V) : V →ₗ[ℂ] ℂ := L.toLinearMap ![0,q] 0
private lemma at_two {V : Type} [AddCommGroup V] [Module ℂ V] (L : MultilinearMap ℂ (fun _ : Fin 2 => V) ℂ) (q p : V) : two L q p = L ![p,q] := by
 rw [two, L.toLinearMap_apply]; exact congrArg _ (funext fun i => by fin_cases i <;> simp [Function.update])

variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book} {d n : ℕ}
lemma fullness (A : Labels.Frames G) {x y : E4} (hx : x≠y) (v : E A d) (hv : v≠0) :
    ∃ b : E A d, disc (fun i => (⟨d,(![v,b] : Fin 2→E A d) i⟩ : (freeTable A).Tag)) (couple x y) ≠ 0 := by
  let p := (exactField A d) v
  have hp : writes A d v≠0 := fun hi => hv ((writes_inj A d) (hi.trans ((writes A d).map_zero.symm)))
  let z : shellSector G d := ⟨pullSol (face (x-y)) (barPol p.val),sector_rot (sector_bar p.property) _⟩
  let b := (exactField A d).symm z
  refine ⟨b, ?_⟩
  rw [disc,writes_eval]
  have hw : writes A d b=z.val := congrArg Subtype.val ((exactField A d).apply_symm_apply z)
  convert ne_of_gt ((reflected_positive hx _).2 hp)
  rw [duplex,aligned_apply,Extra.FD.join]
  apply congrArg _
  ext1 i; fin_cases i <;> first | exact hw | rfl

private lemma point_conv {b : Final C I S} {X : Scaling S} (h : FirstExtension b X) {r : ℕ}
    (q : Fin r → (freeTable C.labels).Tag) (w : Fin r → Bool) (ij : Fin r → Axis × Axis) {z : Points r} (hz : z∈conf r) :
    Tendsto (fun k => Ward.disc (scaledPhysical X b.sector.energy k q w ij) (X.r k • z)) atTop (𝓝
      (Ward.disc (freeWithStress C.labels q w ij) z)) := by
  refine Metric.tendsto_nhds.mpr (fun ε he => (h.jets r 0 q w ij isCompact_singleton (singleton_subset_iff.mpr hz) (half_pos he)).mono fun i hi => ?_)
  rw [dist_eq_norm]; refine le_trans ?_ (hi z (mem_singleton _)) |>.trans_lt (half_lt_self he)
  let A := iteratedFDeriv ℝ 0 (fun y:Points r=>disc (scaledPhysical X b.sector.energy i q w ij) (X.r i•y)) z - iteratedFDeriv ℝ 0 (disc (freeWithStress C.labels q w ij)) z
  have h0 := A.le_opNorm (0:Fin 0→Points r)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at h0
  exact h0
variable {b:Final C I S} {X : Scaling S} (h : FirstExtension b X)
private def sitePair := couple 0 (basis timeAxis)
private lemma apart : (0:E4)≠basis timeAxis := by
  intro hx; have he : (0:ℝ)=basis timeAxis timeAxis := congrArg (fun p : E4 => p timeAxis) hx
  simpa using he
private lemma pair_ok : sitePair∈conf 2 := couple_ok apart
private def actualL (X : Scaling S) (k : ℕ) (v : E C.labels 4) : E C.labels 4 →ₗ[ℂ] ℂ :=
  two ((S.classMoment S (fun _ : Fin 2=>4) (X.r k•sitePair)).compLinearMap (fun _=> (X.U k 4).toLinearMap)) v
private def freeL (C : Family G) (v : E C.labels 4) : E C.labels 4 →ₗ[ℂ] ℂ :=
  two ((freeTable C.labels).classMoment (freeTable C.labels) (fun _ : Fin 2=>4) sitePair) v
def movingTensor (b:Final C I S) (X : Scaling S) (i j : Axis) k :=
   (X.U k 4).symm ((↑(X.r k^4 : ℝ) : ℂ) • b.sector.energy i j)
include h
private lemma plain_pairs (v p : E C.labels 4) : Tendsto (fun k=> actualL X k v p) atTop (𝓝 (freeL C v p)) := by
  let q r := (⟨4,(![p,v]:Fin 2→_) r⟩:(freeTable C.labels).Tag)
  simp only [actualL,freeL,at_two]
  exact point_conv h q (fun _=>false) (fun _=>(0,0)) pair_ok

private lemma crossing (i j : Axis) (v : E C.labels 4) :
   Tendsto (fun k=>actualL X k v (movingTensor b X i j k)) atTop (𝓝 (freeL C v (freeStress C.labels i j))) := by
  let q r := (⟨4,(![freeStress C.labels i j,v]:Fin 2→E C.labels 4) r⟩:(freeTable C.labels).Tag)
  let f := freeWithStress C.labels q ![true,false] (fun _=>(i,j))
  let g k := scaledPhysical X b.sector.energy k q ![true,false] (fun _=>(i,j))
  have he : f=q := by ext1 s; fin_cases s <;> exact rfl
  rw [show freeL C v (freeStress C.labels i j)=disc f sitePair by rw [he,freeL,at_two]; rfl]
  have ht k : g k= fun w => (⟨4,X.U k 4 ((![movingTensor b X i j k,v] : Fin 2→E _ 4) w)⟩:S.Tag) := by
     ext1 s; fin_cases s
     · change Sigma.mk 4 _ = Sigma.mk 4 (X.U k 4 ((X.U k 4).symm _)); rw [LinearEquiv.apply_symm_apply]
     exact rfl
  rw [show (fun k=>_)=(fun k=>disc (g k) (X.r k • sitePair)) from funext fun k=> by rw [ht,actualL,at_two]; rfl]
  exact point_conv h _ _ _ pair_ok
/-- FirstExtension's mixed jets pin the normalized tensor itself as a vector in these moving free coordinates. Includes the additive unit direction. -/
theorem stress_readback (i j : Axis) :
     Tendsto (fun k => (X.U k 4).symm ((↑(X.r k^4 : ℝ) : ℂ) • b.sector.energy i j)) atTop (𝓝 (freeStress C.labels i j)) := by
  let t := movingTensor b X i j
  let t₀ := freeStress C.labels i j
  change Tendsto t atTop (𝓝 t₀)
  suffices he : Tendsto (fun k=> t k - t₀) atTop (𝓝 (0:E C.labels 4)) from
     (show (0:E C.labels 4)+t₀=t₀ from zero_add _) ▸ ((he.add (tendsto_const_nhds (x:=t₀))).congr fun k=>sub_add_cancel ..)
  have hf (v : E C.labels 4) : v≠0 → ∃ b, freeL C b v ≠0 := by simp_rw [freeL,at_two]; exact fullness _ apart v
  exact moving_zero (plain_pairs h) hf fun w=>by
    simp only [map_sub]
    simpa only [t,t₀,sub_self] using ((crossing h i j w).sub (plain_pairs h w (freeStress C.labels i j)))
end YM.Pert.Scale
