import YM.Work.B15
import YM.Work.B16
import YM.MergeProof.North.Brim
import YM.Contacts.Costar.Duo
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Costar
open Function Set Filter Extraction Extraction.Spin Cells Lattice Wilson Next.Phase MergeProof.Ribbons Bid Work.B15
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G){b k l N p : ℕ}(e:b≤ k)

lemma step_trans {n:Side} (T:Tiling n)(x:Site n) (t j:ℕ) : T.copyMap (addr T t j) x= x + T.units.root (addr T t j) := by
  have hb : T.bias (addr T t j)=0 := by ext1 i; simp [Tiling.bias,addr_even]
  unfold Tiling.copyMap affine Tiling.translateBy; rw [hb, addr_even, Signed.act_one, Signed.act_one, Tiling.starts, add_sub_cancel_left,add_zero]
lemma addr_root' (o)(hk:k ≤ N)(t j:ℕ):
    let T:= (center C.S p (e.trans hk) 0).newly o; T.units.root (addr T t j)= location C.S k N p (Episode.step C e t j):= addr_root C e hk p t j
lemma which_after (o) (hk:k ≤ N)(t j:ℕ) (hh: (0:Site (C.side N p))∈ ((center C.S p (e.trans hk) 0).newly o).chamber 0):
    let T:= (center C.S p (e.trans hk) 0).newly o; location C.S k N p (Episode.step C e t j)∈ T.chamber (addr T t j):=by intro T; rw [← addr_root' C e o hk t j]; have he:= T.enumerate (addr T t j) hh; rwa [step_trans T,zero_add] at he
lemma inside_shifted (o)(hk:k ≤ N)(v)(hl:l ≤ N)(tiles: b ≤ l) (x:Site (C.side N p))(t j r:ℕ)
    (hh: Next.Phase.Inside ((center C.S p hl 0).newly v) r x)
    (hi:v=o) : Next.Phase.Inside ((center C.S p hl 0).newly v) r (x+location C.S k N p (Episode.step C e t j)):= by
  subst o; let T:= (center C.S p (e.trans hk) 0).newly v; let Y:= (center C.S p hl 0).newly v
  rw [← addr_root' C e v hk]; rw [← step_trans T x]
  exact (inside_reflected T Y rfl (Around.inherits (C:=C) tiles hl) rfl rfl (addr T t j) r x).2 hh
lemma know_location (F:Extraction.Order)(x y:Cover)(h: 2*C.S.a b < ‖C.S.gridPoint k x-C.S.gridPoint k y‖) : ∀ᶠ i:ℕ×ℕ in F.fuse, ∀ he:b ≤ i.1,
    span C.S he i.2 < separation (location C.S k i.1 i.2 x) (location C.S k i.1 i.2 y):= by
  rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually (faraway C k (x-y))] with p hp; filter_upwards [F.mesh.cofinal.eventually_ge_atTop k] with i hi he
  let q:= F.per p; let n:= F.mesh i; change k≤ n at hi; change b≤ n at he
  let X:= location C.S k n q x-location C.S k n q y
  have hx:X=(C.S.toDepth hi q).embed (wrap (C.side k q) (x-y)):= by unfold X location; rw [dif_pos hi,dif_pos hi,map_sub]; simp_rw [← Ratio.root_embed,map_sub]
  have hs: C.S.place X=C.S.gridPoint k x-C.S.gridPoint k y:=by
      rw [hx,C.S.embeds_place]; exact hp.trans (by ext; simp [Schedule.gridPoint,mul_sub])
  have ht:= (normC C n q X).2
  have hv : separation X 0=separation (location C.S k n q x) (location C.S k n q y):=by unfold separation; rw [sub_zero]
  rw [hs,hv] at ht; have hL : C.S.a n* ↑(span C.S he q)= C.S.a b:= C.S.embeds_scale (C.S.toDepth he q)
  apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left (a:=2*C.S.a n) _ (by have h:=C.S.a_pos n; positivity); rw [mul_assoc]; change (2:ℝ)*(C.S.a n* ↑(span C.S he q)) < _; rw [hL]
  exact h.trans_le ht
-- payments use fixed t past strict; no contiguous rate in t
lemma grid_step (t j:ℕ)(a:Axis) : C.S.gridPoint k (Episode.step C e t j) a =
    C.S.a k*((C.S.toDepth e 0).count.val:ℝ)*(2*t*j):=by simp [Schedule.gridPoint,Episode.step]; ring
lemma slide_far (j i:ℕ)(h:i≠j)(x y:Cover)(r:ℝ) : ∀ᶠ t in atTop,
    r < ‖C.S.gridPoint k (x+Episode.step C e t j) - C.S.gridPoint k (y+Episode.step C e t i)‖ := by
  have he j i (h:i<j) (x y:Cover) : ∀ᶠ t in atTop, r < ‖C.S.gridPoint k (x+Episode.step C e t j) - C.S.gridPoint k (y+Episode.step C e t i)‖ := by
      let a (t:ℕ):= C.S.gridPoint k (x+Episode.step C e t j) - C.S.gridPoint k (y+Episode.step C e t i)
      let d t:=a t timeAxis
      let κ:ℝ:= (C.S.a k)*(↑(C.S.toDepth e 0).count.val)*(2*(j-i)) -- nat subtraction? annotate
      have ht:0<κ:=mul_pos (mul_pos (C.S.a_pos k) (by exact_mod_cast (C.S.toDepth e 0).count.property)) (by exact mul_pos (by norm_num) (sub_pos.mpr (by exact_mod_cast h)))
      have he t:d t=κ*t+(C.S.gridPoint k x timeAxis-C.S.gridPoint k y timeAxis):=by unfold d a; rw [Work.B16.grid_add,Work.B16.grid_add]; simp only [PiLp.add_apply,PiLp.sub_apply,grid_step]; unfold κ; ring
      have hD : Tendsto d atTop atTop:= (tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop ht)).congr fun t=> (he t).symm
      filter_upwards [hD.eventually_gt_atTop r] with t ht
      exact ht.trans_le ((Real.le_norm_self _).trans (PiLp.norm_apply_le ..))
  rcases lt_or_gt_of_ne h with h|h; exact he _ _ h x y
  filter_upwards [he i j h y x] with t hp; rwa [norm_sub_rev] at hp
lemma slide_grid (t:Cover)(x y:Cover): C.S.gridPoint k (x+t) - C.S.gridPoint k (y+t)= C.S.gridPoint k x-C.S.gridPoint k y:= by simp_rw [Work.B16.grid_add]; abel
lemma zero_grid : C.S.gridPoint k 0=0 := by ext; simp [Schedule.gridPoint]
theorem seats_grid {l κ m:ℕ} (F:Extraction.Order)(y:Fin m → Cover)
    (h:∀ i, 2*C.S.a b < ‖C.S.gridPoint k (y i)‖)
    (hY:∀ i j,i≠j→ 2*C.S.a l < ‖C.S.gridPoint k (y i)-C.S.gridPoint k (y j)‖):
    ∀ᶠ t in atTop, ∀ᶠ c:ℕ×ℕ in F.fuse,
      let p i:=location C.S k c.1 c.2 (Episode.step C e t i)
      let η (j: Fin κ×Fin m):= location C.S k c.1 c.2 (y j.2)+p j.1.val
      (∀ i: Fin κ, ∀ j, ∀ he:b ≤ c.1, span C.S he c.2 < separation (p i.val) (η j)) ∧
      (∀ i j,i≠j→ ∀ he:l ≤ c.1, span C.S he c.2 < separation (η i) (η j)):= by
   have hx (i:Fin κ)(j:Fin κ× Fin m): ∀ᶠ t in atTop, 2*C.S.a b < ‖C.S.gridPoint k (Episode.step C e t i.val)-C.S.gridPoint k (y j.2+Episode.step C e t j.1.val)‖:= by
       by_cases he:i=j.1
       · subst i; exact Eventually.of_forall fun t=> by simpa only [zero_add,zero_grid,zero_sub,norm_neg] using ((show 2*C.S.a b < ‖C.S.gridPoint k ((0:Cover)+Episode.step C e t j.1.val)-C.S.gridPoint k (y j.2+Episode.step C e t j.1.val)‖ from by rw [slide_grid,zero_grid,zero_sub,norm_neg]; exact h _))
       simpa only [zero_add] using slide_far C e i.val j.1.val (Ne.symm (Fin.val_injective.ne he)) 0 (y j.2) (2*C.S.a b)
   have hv (i j:Fin κ×Fin m)(he:i≠j) : ∀ᶠ t in atTop, 2*C.S.a l < ‖C.S.gridPoint k (y i.2+Episode.step C e t i.1.val) - C.S.gridPoint k (y j.2+Episode.step C e t j.1.val)‖:=by
       by_cases hh:i.1=j.1
       · simp_rw [hh, slide_grid]; exact Eventually.of_forall fun t=> hY _ _ fun hE=>he (Prod.ext hh hE)
       exact slide_far C e _ _ (Fin.val_injective.ne (Ne.symm hh)) (y i.2) (y j.2) (2*C.S.a l) -- hh type ≠
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=> hx i j,eventually_all.mpr (fun i=> eventually_all.mpr fun j=> eventually_all.mpr (hv i j))] with t ht hs
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=> know_location C F _ _ (ht i j), eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun h=> know_location C F _ _ (hs i j h)] with c hi hp
   simp_rw [Extraction.Order.location_add] at hi hp
   exact ⟨hi,hp⟩
end YM.Contacts.Costar
