import YangMills.WilsonProof.NativeSupport.YM.MS.Wilson.Space
/-!
# Sections in any port list

Kernel f analytic in few link variables. Compose ports to write cylinder.
   Wrap recover seams. Don't assume translational invariance from raw kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Sew
open Function Filter Finset Set Plane Koszul Cylinder Taylor Lab Lattice
open scoped Topology ContDiff
variable {A:Type} {P Q:Type} {G:Gauge}[Fintype A][DecidableEq A]

def knot (W:A→Edge P)(u:A×Conn G): LightMode G P:= formAt (W u.1).2 u.2 (W u.1).1
variable (W:A→Edge P)
-- port map

def art (W:A→Edge P)(f:Lot G A→ℝ) : Dot G P:= Ferry (knot W) (region.symm (ink priv f))
def thread (r:P→Q)(W:A→Edge P): A→Edge Q:=fun i=> (r (W i).1,(W i).2)
lemma map_sec (r:P→Q)(f:Lot G A→ℝ): transport r (art W f) = art (thread r W) f:= by unfold art transport; rw [ferry_trans]; rfl

variable [DecidableEq P]

omit [Fintype A][DecidableEq A] in
lemma knot_way (i:LightMode G P)(j:A×Conn G): projector j (direction i ∘ W) = way (knot W) i j := by
    rw [projector_k]; rcases i with ⟨⟨⟨_|a,_|_⟩,u⟩,x⟩ <;> try (rw [need _ (by simp [knot,formAt,Landau.gauge])]; rfl)
    rcases j with ⟨j,v⟩; by_cases he:(x,a)=W j; swap
    · rw [need _ ?h]; swap
      · intro H; apply he; have h := congr_arg Prod.snd H; have h' := congr_arg (Option.getD · a) (congr_arg (fun i:LightMode G P=> i.1.1.1) H); exact Prod.ext h h'
      simp [direction,priv,  Ne.symm he]
    by_cases hv:u=v; swap
    · rw [need _ (fun H=> hv (congr_arg (fun i:LightMode G P=>i.1.2) H))]; simp [direction,priv, baseC,he,Ne.symm hv]
    rw [show (( ( (some a,false),u),x):LightMode G P)= knot W (j,v) from by subst v; rw [knot]; unfold formAt; rw [show W (j,u).1=(x,a) from he.symm]] -- `rfl`
    rw [only]; simp [knot,direction,formAt, Landau.gauge,priv, baseC]
lemma consult (i:LightMode G P): (direction i ∘ W)=∑ j:A×Conn G,way (knot W) i j (R:=ℝ) • priv j:= by
    nth_rw 1 [← frame (direction i ∘ W)]; exact Finset.sum_congr rfl fun j _=> by rw [knot_way]

variable [Fintype P]
def pull (W:A→Edge P) : Lot G (Edge P)→L[ℝ] Lot G A:= ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (W i)
omit [Fintype A][DecidableEq A][DecidableEq P][Fintype P] in
lemma pulled (W:A→ Edge P)(x: Lot G (Edge P)): pull W x=x ∘ W:=rfl
lemma pooled {f:Lot G A→ℝ}(h:germ f): (art W f).val= reads (f ∘ pull W):= by
    rw [reads,ink_ctrl_one direction (pull W) h, ferry_pulls (r:=knot W) priv (pull W ∘ direction) ?h h]; rfl
    intro i; exact consult W i
-- covers alias exactly since wrap tied
omit [Fintype P][DecidableEq P] in
lemma enters_gorge {n:Side} (W:A→Edge Cover)(f:Lot G A→ℝ)(h:germ f) : enters n (art W f)=reads (f ∘ pull (thread (wrap n) W)):= by change (transport _ _).val=_; rw [map_sec,pooled _ h] -- simp alias
-- convenience lemmas single-axis local link port via unit

end YM.MS.Native.Sew
