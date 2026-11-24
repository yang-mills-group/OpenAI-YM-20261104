import YM.UVExt.PowerFlow
/-! One map comparison shares stencil limits over ALL ordinals `p`. Extracting them is for testing sublimits only, not choosing a UV subsequence as the convergence conclusion. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Exterior Laurent Bid Tree Filter Set Real Next.Free Bloch Matrix Work.F08
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (A : Levels G) (M : Horizon A) (P : MapPrices)

section frameeq
variable {α β : Type*} [Fintype α] [Fintype β] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private lemma t_frame {F} (K : Matrix α β ℝ) {v : F→β→E} {p q} (hp : Tendsto v p (𝓝 q)) : Tendsto (fun i=>actionFrame K (v i)) p (𝓝 (actionFrame K q)) := tendsto_pi_nhds.mpr fun i=> tendsto_finsetSum _ fun j _=> Tendsto.const_smul (tendsto_pi_nhds.mp hp _) _ -- order invert?
variable {t : Side}
private lemma color_frame (v : Dir G t) : actionFrame (d 1 t) v=dColor G t 1 v := frame_ext fun i=> frame_color 2 1 _ v i
lemma t_color {F} {v : F→Dir G t} {p q} (hp : Tendsto v p (𝓝 q)) : Tendsto (fun i=>dColor G t 1 (v i)) p (𝓝 (dColor G t 1 q)) := by
  change Tendsto (dColor G t 1 ∘ v) p (𝓝 (dColor G t 1 q))
  rw [←funext (color_frame (t:=t) (G:=G))]
  exact (show _ from t_frame (d 1 t) hp)
end frameeq

-- trajectory gate and mesh quote must be threaded on the same receipts.
structure Discipline (P : MapPrices) (A : Levels G) (M : Horizon A) : Prop where
   plan : M.Suffices P
   figure : ∃ l : ℕ→ℕ→ℝ, Figure P A M l ∧ ∀ i, ∃ z, ∀ N, i < N → l N i=z
   gate : TowerGate A P
   symmetry : ∀ N m t, m < N → Sworn (M.H N m) (A.S.side m t) G

abbrev Transfers (i) := Cross (A.S.block i) (TypeFace 1) (TypeFace 1)
def parcels (u : ℕ→ℕ) (j : ℕ) i : Transfers A i := (M.towers (u j) i).A0
variable {u : ℕ→ℕ} (hu : Tendsto u atTop atTop)
structure Follows (u : ℕ→ℕ) (M : Horizon A) (U : ∀ i, Transfers A i) : Prop where
   entries (i) : Tendsto (parcels A M u · i) atTop (𝓝 (U i))
   installs (i p) : Tendsto (fun x=>selectedMatrix A M (u x) i p) atTop (𝓝 (installed (A.clock.op i p).ratio (U i)))
     -- replace composition syntax. U i count dependent
variable (Q : Discipline P A M)
include hu Q
set_option linter.unusedSectionVars false
-- include parameters dependency order inspect after
set_option maxHeartbeats 250000 in
lemma Assurance : ∃ f: ℕ→ℕ,StrictMono f ∧ ∃ U,Follows A (u ∘ f) M U := by
    let hP := Q.plan
    let ν := Σ i:ℕ, (Co (A.S.block i) (TypeFace 1)) × TypeFace 1 × Cover -- sigma notation?
    let K (j : ℕ) (v:ν) := parcels A M u j v.1 v.2.1 v.2.2.1 v.2.2.2
    have hB (i) {j} (hj : i<u j) : Row.strip (parcels A M u j i) (P.α (A.clock.J (i+1))) (P.Ω (A.clock.J (i+1)) / (A.S.block i).val) := by
      have hs := (hP.costs (u j) i hj).2.2.2 [] (Nat.zero_le _)
      simpa only [parcels,advanceC,List.length_nil,add_zero,pow_one] using hs.1
    let C (i:ν) := Next.Free.UV.flotilla (P.α (A.clock.J (i.1+1))) ((P.Ω (A.clock.J (i.1+1)))/ (A.S.block i.1).val) i.2.2.2
    obtain ⟨U,k,hk,hU⟩ := sequence_extract (u:=K) (restrain _ (C:=C) fun i=> (hu.eventually (eventually_gt_atTop i.1)).mono fun j hj => Next.Free.UV.width_flot (hB i.1 (by exact hj)) _ _ _)
    let V (i) : Transfers A i := fun z t x=> U ⟨i,z,t,x⟩
    have hR i : Tendsto (fun j=> parcels A M (u∘k) j i) atTop (𝓝 (V i)) := tendsto_pi_nhds.mpr fun _=>tendsto_pi_nhds.mpr fun _=>tendsto_pi_nhds.mpr fun _=>tendsto_pi_nhds.mp hU ⟨i,_,_,_⟩
    refine ⟨k,hk,V, hR,fun i p=>tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=> ?_⟩
    have hw := Next.Free.UV.tendsto_entries (hR i) (P.alpha_pos (A.clock.J (i+1))) (hk.tendsto_atTop.eventually ((hu.eventually (eventually_gt_atTop i)).mono fun t ht=> hB i ht)) (A.S.side i p)
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hw _) _

omit hu Q in
lemma Follows.subseq {A : Levels G} {M : Horizon A} {u : ℕ→ℕ} {U : ∀ i, Transfers A i} (h : Follows A u M U) {k: ℕ→ℕ} (hk : Tendsto k atTop atTop) : Follows A (u ∘ k) M U := by refine ⟨fun i=> (h.entries i).comp hk,fun i s=> (h.installs i s).comp hk⟩

def mapBind (M : Horizon A) (U : ∀ i, Transfers A i) : Roller A := fun i p=> polish (installed (A.clock.op i p).ratio (U i))
lemma Follows.bottom {U} (hU : Follows A u M U) (i p) (v : Dir G (A.S.side i p)) :
     let D:=towerPrice A.clock.kernel.penalty P (A.clock.J (i+1)) (A.clock.J i); let L:=A.S.block i
   ‖mapBind A M U i p v‖ ≤ D/L.val * ‖v‖ ∧ ‖dColor G _ 1 (mapBind A M U i p v)‖ ≤ D/(L.val:ℝ)^2 *‖dColor G _ 1 v‖ ∧ gradD (mapBind A M U i p v) ≤ D/(L.val:ℝ)^3 * gradD v := by
 intro D t
 let f j := polish (selectedMatrix A M (u j) i p) v
 have hF : Tendsto f atTop (𝓝 (mapBind A M U i p v)) := polish_tends v (hU.installs i p)
 obtain ⟨l,H₁,-⟩ := Q.figure
 have hi := hu.eventually (eventually_gt_atTop i)
 have hh := hi.mono fun j hj => cost_one P M (hM:=Q.plan) (u j) i p (show i<u j from hj) v H₁
 have hD := t_color hF
 have hx (z : Axis) : Tendsto (fun j=>deltaV z (f j)) atTop (𝓝 (deltaV z (mapBind A M U i p v))) := t_frame _ hD
 exact ⟨le_of_tendsto hF.norm (hh.mono fun j hj=> hj.1),le_of_tendsto hD.norm (hh.mono fun j hj=>hj.2.1), le_of_tendsto ((show Tendsto (fun j z=>deltaV z (f j)) atTop (𝓝 _) from tendsto_pi_nhds.mpr hx).norm) (hh.mono fun i hi=>hi.2.2)⟩
end YM.UVExt.Paths
