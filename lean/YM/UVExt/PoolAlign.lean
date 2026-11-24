import YM.UVExt.WaveCost
import YM.Work.F08.Rows

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Real Wilson Precision Lattice Bid Exterior Set Matrix Laurent Bloch
open Work.F08
open Next.Free.UV
open scoped BigOperators Classical Topology ContDiff

section grouping
variable {ι α β γ δ : Type*} (s : α→β) (t : β→γ) {f : α → ℝ}
lemma spread {g : α→ℝ} {u : α→β} (hg : Summable g) : HasSum (pool g u) (∑' j,g j) := by
  have ht := hg.hasSum.tsum_fiberwise u
  exact ht

lemma pool_mask (j) : pool f s j = ∑' (x : α), if s x=j then f x else 0 := by
  classical
  unfold pool; rw [show (∑' (i:{i:α//s i=j}), f i)=∑' y,(s⁻¹'({j}:Set β)).indicator _ y from tsum_subtype _ _]; rfl -- u unbound fix

set_option maxHeartbeats 400000 in
lemma push_twice (hf : Summable f) (j) : pool f (t ∘ s) j = pool (pool f s) t j := by
  classical
  simp_rw [pool_mask]
  change (∑' i, if t (s i)=j then f i else 0)=_; rw [←(show Summable (fun i=>if t (s i)=j then f i else 0) from hf.indicator ((t∘s)⁻¹'({j}:Set γ))).hasSum.tsum_fiberwise s |>.tsum_eq]
  refine tsum_congr fun i=> ?_
  by_cases h : t i=j
  · rw [if_pos h]
    refine Eq.trans (tsum_congr fun x => by exact if_pos ((congr_arg t x.property).trans h)) (pool_mask s i)
  rw [if_neg h]; change (∑' (u:{a//s a=i}),if t (s u)=j then _ else _)=_; exact Eq.trans (tsum_congr (fun (u:{a// s a=i}) => if_neg (fun (hx : t (s u)=j) => h (Eq.trans (congr_arg t u.2.symm) hx)))) tsum_zero

lemma outer_pool {w : β→δ} {s : α→γ} {f : α→ℝ} {p : β→ℝ} (hf : Summable (‖f ·‖)) (hp : Summable (‖p ·‖)) (i) (j) :
    pool (fun i : α×β=> f i.1*p i.2) (Prod.map s w) (i,j) = pool f s i * pool p w j := by
  classical
  simp_rw [pool_mask]; rw [tsum_mul_tsum_of_summable_norm]; apply tsum_congr; intro u
  by_cases h : s u.1=i <;> by_cases h' : w u.2=j <;> simp [Prod.map,h,h']
  · exact hf.of_norm.indicator {a|s a=i} |>.norm
  · exact hp.of_norm.indicator {i|w i=j} |>.norm

end grouping

abbrev Spot := Cover×PlaqAxes
abbrev Rel := PlaqAxes×PlaqAxes×Cover

def placeSlot (i : Slot) : Spot := (i.offset,i.plaq)
def placeRelative (i : Slot×Slot) : Rel := (i.1.plaq,i.2.plaq,i.2.offset-i.1.offset)
def reduced (W : Slot×Slot→ℝ) := pool W placeRelative

def savePlane {G : Gauge} (K : Rel) (i : G.ColorIndex) : Token G 2 := ⟨![⟨[],K.1⟩,Stationary.walkSlot K.2.1 K.2.2],fun _=>i⟩
lemma save_shell {G : Gauge} (i : Chord G) : savePlane (placeRelative i.1) i.2 = shell false i := rfl

section anchor
variable {G : Gauge} {σ C Λ : ℝ}

lemma reduced_air {N : Side} (W : Slot×Slot→ℝ) (hr : Weighted C σ (fun k : Chord G=> W k.1)) (he : 0<σ) (x) (v : Dir G N) (t : ℝ) : HasSum (fun i=> reduced W i * ∑ j:G.ColorIndex, stream v x (savePlane i j) t)
    (liftAir v false x (fun (i : Chord G)=>W i.1) t) := by
  let f (i : Slot×Slot) := W i * ∑ j:G.ColorIndex, stream v x (savePlane (placeRelative i) j) t
  let g (i : Chord G) := W i.1*stream v x (shell false i) t
  have hg : Summable g := (air_sum v false x hr he t 0).1
  have h i : f i = ∑' j,g (i,j) := by rw [tsum_fintype]; unfold g f; rw [Finset.mul_sum]; rfl
  have hf : Summable f := by rw [show f=fun _=> _ from funext h]; exact hg.prod
  have hS := spread (u:=placeRelative) hf; unfold pool at hS
  change HasSum _ (∑' i,g i)
  rw [hg.tsum_prod, show (∑' (i:Slot×Slot),∑' j,g (i,j))=_ from tsum_congr (fun i=>(h i).symm)]
  convert hS using 1
  funext i; unfold reduced pool; rw [←tsum_mul_right]; apply tsum_congr
  intro j; unfold f; rw [j.property]

set_option maxHeartbeats 100000 in
lemma layout_row (M : Bed) (R : PathData G) (ht : Attached M R) {p : Clip} (hb : R.Bounds p σ C Λ) (a b : PlaqAxes) (d : Cover) :
    pool (ink R a) placeSlot (d,b) = M.roots (plaquette a) (plaquette b) d := by
  let f i := (R.row a i).1
  have hW := raw_money hb a
  have hf : Summable f := (Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp <| mul_nonneg hb.width.le (hW.1 i))) hW.paid.2.1).of_norm
  change pool (pool f _) _ _= _; rw [←push_twice _ _ hf _,pool_mask]
  convert (ht.layout a b d).tsum_eq using 1
  refine tsum_congr fun i=>?_; by_cases h: (R.row a i).2.offset=d <;> by_cases h': (R.row a i).2.plaq=b <;> simp_all [placeSlot,f]

-- for all limits, not just those literally ink of a PathData
lemma reduced_eval (W : Slot→ℝ) (hb : Carries C σ SlotSize W) (he : 0 < σ) (a b : PlaqAxes) (d : Cover) :
    reduced (fun q=>W q.1*W q.2) (a,b,d) = ∑' u, pool W placeSlot (u,a)* pool W placeSlot (d+u,b) := by
  let s := Prod.map placeSlot placeSlot
  let t := fun (p : Spot×Spot) => (p.1.2,p.2.2,p.2.1-p.1.1)
  let f := fun q : Slot×Slot=> W q.1*W q.2
  change pool f (t∘s) _= _
  have hW' := hb.paid.2.1.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp <| mul_nonneg he.le (hb.1 i)))
  have hh : Summable f := summable_mul_of_summable_norm hW' hW'
  have hf := spread (u:=s) hh
  let Q := {z : Spot×Spot//t z=(a,b,d)}
  let e : Q ≃ Cover := {
    toFun z := z.val.1.1
    invFun u := ⟨((u,a),(d+u,b)),Prod.ext rfl (Prod.ext rfl (add_sub_cancel_right ..))⟩
    left_inv z := Subtype.ext (Prod.ext (Prod.ext rfl (congr_arg Prod.fst z.property).symm) (Prod.ext (show _ by have ht := congr_arg (fun p : Rel=>p.2.2) z.property; change z.val.2.1-z.val.1.1=d at ht;  exact (congr_arg (· + z.val.1.1) ht).symm.trans (sub_add_cancel ..)) (congr_arg (fun p : Rel => p.2.1) z.property).symm))
    right_inv z := rfl }
  let g (z : Spot×Spot) := pool W placeSlot z.1 * pool W placeSlot z.2
  have hg' (zz : Spot×Spot) : pool f s zz = g zz := outer_pool hW' hW' _ _
  conv_lhs => rw [push_twice _ _ hh]
  unfold pool -- maybe not recursively? unfold all both sides
  change (∑' z:Q,pool f s z.val)=_
  rw [show (∑' z : Q,pool f s z)=∑' z, pool f s (e.symm z) from Eq.symm <| Equiv.tsum_eq e.symm (fun z : Q=>pool f s z)] -- need change
  refine tsum_congr fun z=>hg' _

lemma reduced_root {M : Bed} {W : PlaqAxes→Slot→ℝ} (ht : ∀ b a d,pool (W b) placeSlot (d,a)=M.roots (plaquette b) (plaquette a) d)
    (hb : ∀ b,Carries C σ SlotSize (W b)) (he : 0 < σ) (a b : PlaqAxes) (d : Cover) :
    (∑ k, reduced (fun q=> W k q.1*W k q.2) (a,b,d)) = composeRows (transRows M.roots) M.roots (plaquette a) (plaquette b) d := by
  simp only [composeRows,routed]
  conv_rhs => rw [←Equiv.sum_comp plaqEquiv]
  apply Finset.sum_congr rfl
  intro u _
  rw [reduced_eval (W u) (hb u) he a b d, ← (Equiv.neg Cover).tsum_eq (fun x => transRows M.roots (plaquette a) (plaqEquiv u) x * M.roots (plaqEquiv u) (plaquette b) (d-id x))]; refine tsum_congr fun y => ?_
  rw [ht,ht, transRows,Equiv.neg_apply]
  change _ = M.roots (plaqEquiv u) (plaquette a) (- -y)*M.roots (plaqEquiv u) (plaquette b) (d- -y); rw [neg_neg,sub_neg_eq_add]; rfl

lemma budget_root (M : Bed) (W : PlaqAxes→Slot→ℝ) (ht : ∀ b a d,pool (W b) placeSlot (d,a)=M.roots (plaquette b) (plaquette a) d)
    (hb : ∀ b,Carries C σ SlotSize (W b)) (he : 0 < σ) : M.roots.strip σ C := by
  intro a b
  obtain ⟨u,rfl⟩ := plaqEquiv.surjective a
  obtain ⟨v,rfl⟩ := plaqEquiv.surjective b
  have hg (a : Slot) : (Laurent.size (placeSlot a).1 : ℝ) ≤ SlotSize a := Nat.cast_le.mpr ((length_offset a).trans (Nat.le_add_right ..))
  have hc := pool_money (L':=fun z : Spot=> (Laurent.size z.1)) (s:=placeSlot) (hb u) he hg (fun z=>Nat.cast_nonneg _)
  refine (show Carries C σ (fun x:Cover => (Laurent.size x:ℝ)) (M.roots (plaquette u) (plaquette v)) from ?_).paid
  refine ⟨fun _=> Nat.cast_nonneg _,fun s=>?_⟩
  let emb : Cover ↪ Spot := ⟨fun u=> (u,v),fun i j h=>congr_arg Prod.fst h⟩
  have ht' := hc.2 (s.map emb); rw [Finset.sum_map] at ht'
  simp_rw [ht] at ht'; exact ht'

end anchor
end YM.UVExt.Paths
