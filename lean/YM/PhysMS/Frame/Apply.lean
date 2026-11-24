import YM.OPE.Levy.Measured
import YM.PhysMS.Frame.Cost
import YM.PhysMS.Frame.Tensor

/-! Keep all the cost in a multilinear reading when moving the slots in the
whole *continuously-scaled* tower. Propagation method in `OPE.Levy.evaluated`;
here with the new all-length rate and preserving that horizon pull.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Spec OPE OPE.Orbits Climb Levy Trace.Pilot
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} (F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (U:ℝ→tower S) (H:Leading F U)
local notation "Q" => F.sector.derivatives
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d
variable {I J W : Type} [Fintype I] {v: I → ℕ} {l: Filter J} {r:J→ℝ} (hr:Tendsto r l trail)
include H hr R
lemma entrust (d m:ℕ)(hm:m≤d)(x:D d): RateLE l (LogV ∘ r)
    (fun i:J=> R.cutTest m d (U (r i) d x)) (-(m:ℝ)):= by
    let p:= LinearMap.toContinuousLinearMap (R.cutTest m d)
    have hp := (upper F d U H m hm p ?_).comp hr
    swap; · cases m with
            | zero => intro y hy; rw [show y=0 from (Submodule.mem_bot ..).mp hy,map_zero]
            | succ m=> intro y hy; obtain ⟨u,rfl⟩:= hy; unfold p; change R.cutTest (m+1) d _=0; rw [R.cut_rise]; exact R.kills_lower _ _ (Nat.lt_add_one _) _
    have hx:= (RateLE.norm (X:=(Bel C.book).Field d→L[ℂ] S.Field m) hp).mul (RateLE.const ‖x‖ (to_log_zoom.comp hr))
    rw [add_zero] at hx; exact hx.of_norm_le (Eventually.of_forall fun i=> (pulling d U p (r i)).le_opNorm x)

lemma total [NormedAddCommGroup W] [NormedSpace ℂ W] (p:(i:I)→(Bel C.book).Field (v i)) (A:ℝ)
    (M:J→∀ d : I→ℕ, MultilinearMap ℂ (fun i=> S.Field (d i)) W)
    (hv:∀ d:I→ℕ,∀ h:d≤v, ∀ᶠ i in l,∀ u:(k:I)→ S.Field (d k), M i d u=M i v (fun j=>(Q).rise (h j) (u j)))
    (hw:∀ d:I→ℕ,d≤v→∀ u:(k:I)→S.Field (d k), RateLE l (LogV ∘ r) (fun i=>M i d u) (weight d + A)) :
    RateLE l (LogV ∘ r) (fun i=>M i v (fun j=> U (r i) (v j) (p j))) A := by
     let K:=fun i=>Fin (v i+1)
     let cost(j:(i:I)→K i):I→ℕ:=fun i=>(j i).val
     let b (i:J)(k:I):=U (r i) (v k) (p k)
     let g(i:J)(k:I)(j:K k):= R.cutTest (j:ℕ) (v k) (b i k)
     let φ(i:J)(k:I)(j:K k):S.Field (v k):= (Q).rise (Nat.le_of_lt_succ j.isLt) (g i k j)
     have ht(i:J): b i=fun k=>(∑ j:K k,φ i k j):=by
       funext t
       change _=∑ j:K t,(Q).rise _ _
       rw [← (Q).arrival R.continuum.laws.toSymmetric R.lifts (b i t)]; exact (R.reconstruct _ _ (Nat.le_refl _) (b i t)).symm
     have hQ(j:∀ i:I,K i):cost j≤v:=fun i=>Nat.le_of_lt_succ (j i).isLt
     have hEq:∀ᶠ i in l,∀ j: (i:I)→K i,M i v (fun k=>φ i k (j k)) = M i (cost j) (fun k=>g i k (j k)):=
        eventually_all.mpr fun j=> (hv _ (hQ j)).mono fun i he=> (he _).symm
     change RateLE _ _ (fun i=>M i v (b i)) _
     refine RateLE.congr (RateLE.sum (f:=fun j i=>M i (cost j) (fun k=>g i k (j k))) (S:=Finset.univ) (to_log_zoom.comp hr) (fun j _=> ?_)) (hEq.mono fun k hk=> by dsimp only; rw [ht k,MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun _ _=>(hk _).symm)
     have hx(t:I):= entrust F R U H hr (v t) _ (hQ j t) (p t)
     have hp:= Orbits.contract (to_log_zoom.comp hr) (fun k=> M k (cost j)) (hw _ (hQ j)) (fun i k=>g i k (j k)) (fun i=>-(cost j i:ℝ)) hx
     rw [Finset.sum_neg_distrib] at hp; exact hp.mono (by unfold weight; exact le_of_eq (by ring))

omit H hr R

/-- Equivalent uniform-power version. Applies also to moving geometries (without shrinking
    the one schedule/forms). -/
lemma uniform_power {P:ℝ→J→Prop} [Nonempty J] {Y:ℝ→J→W} [Norm W] {m ε:ℝ} (he:0<ε)
    (h:∀ (u:ℝ→J) (l:Filter ℝ), l.NeBot → l≤trail → (∀ᶠ i in l, P i (u i)) → RateLE l LogV (fun i=> Y i (u i)) (-m)) :
    ∀ᶠ i in trail, ∀ j, P i j → ‖Y i j‖ ≤ i^(m-ε) := by
    apply refine_geometry; intro u l H hv hp; have ht:= h u l H hv hp
    let g(i:ℝ):= i^(m-ε); have hf:= (length_rate.rpow (m-ε)).shrink hv
    rw [mul_neg, mul_one] at hf
    exact ⟨l,H,le_rfl,hf.outweigh ht (by linarith only [he]) (to_log_zoom.mono_left hv)⟩
lemma pays_power {Y:J→W} [Norm W] {m:ℝ} (h:∀ ε:ℝ,0<ε → ∀ᶠ j in l, ‖Y j‖ ≤ r j ^ (m-ε))
    (hr:Tendsto r l trail): RateLE l (LogV ∘ r) Y (-m) := by
    intro a ha; let b:= (a+m)/2; have he:0<b:= by unfold b; linarith only [ha]
    have H:= (length_rate.rpow (m-b)).comp hr; rw [mul_neg,mul_one] at H
    exact ((H.pays (to_log_zoom.comp hr)).of_norm_le (h b he)) a (by unfold b; linarith only [ha])
end YM.PhysMS.Frame
