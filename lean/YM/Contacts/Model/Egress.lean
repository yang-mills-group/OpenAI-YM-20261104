import YM.Contacts.Model.Stage
/-! Make local mask-free templates by clipping displacements on COVER around slot zero. (Labels ordered.) -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {α:Type} {G:Gauge}{n m c C:Side}{k w r z:ℕ}
section roof
variable [Fintype α] {q:Field (Fin (r+1)) (Node α)} (w)
abbrev Z:= Fin (r+1)
-- displacements. support κ. catalyst.
def stay {α:Type} (w:ℕ)(p: (Fin (r+1)→Node α)) := ∀ i,(p i).1-(p 0).1∈ Lattice.box w
def blockR {α:Type} (w:ℕ)(q:Field (Fin (r+1)) (Node α)) : Field (Fin (r+1)) (Node α):=fun p=> if stay w p then q p else 0
omit [Fintype α] in
lemma blocks_move (h:∀ i,Mirrored (backpack i) q) (i:Cover): Mirrored (backpack i) (blockR w q):= by
   intro p; unfold blockR; rw [h]; apply if_congr _ rfl rfl; unfold stay; refine forall_congr' fun k=>?_ ; change (p k).1+i-((p 0).1+i) ∈ _ ↔ _; rw [add_sub_add_right_eq_sub]
omit [Fintype α] in
lemma scope {σ:ℝ≥0}{e:ℝ}(h:Rooted (terrain σ _) q e): Rooted (Range.cheap _) (q-blockR w q) (Real.exp (-(σ:ℝ)*w)*e):= by
   refine ⟨mul_nonneg (Real.exp_pos _).le h.cash, fun i x=>?_⟩; refine budget_mono (budget_scale (Real.exp_pos _).le (h.row i x)) (fun _=>by positivity) ?_; intro p
   have hh (g): (Range.cheap (Node α)).bill (g : Fin (r+1)→Node α)=1:= by simp [Range.cheap,Range.bill,Range.height] -- inspect
   rw [hh,mul_one]; let X:=p.val; by_cases he:stay w X
   · rw [Pi.sub_apply,show blockR w q p.val = q p.val from if_pos he,sub_self,norm_zero]; positivity
   rw [Pi.sub_apply,show blockR w q p.val = 0 from if_neg he,sub_zero]; rw [mul_left_comm]; apply le_mul_of_one_le_right (norm_nonneg _); unfold stay at he; obtain ⟨j,hj⟩:= not_forall.mp he
   let c:=(X j).1-(X 0).1; have ht : w≤ Laurent.size c:= by
      by_contra! h; refine hj (Lattice.box_test.mpr ⟨fun i=> ?_,fun i=>?_⟩) <;> first | (change -(w:ℤ) ≤ c _; have ht:= FreeResolvent.own_size c i; omega) | (change c _ ≤ (w:ℤ); have ht:= FreeResolvent.own_size c i; omega)
   rw [neg_mul,Real.exp_neg]; apply (one_le_inv_mul₀ (Real.exp_pos _)).mpr
   apply le_trans _ ((terrain σ _).width X 0 j); rw [terrain_step]; apply Real.exp_monotone; gcongr

-- explicit finite compression catalog
abbrev SliceIdx (α:Type): Type:= (Fin (r+1)→ ↥(Lattice.box w) × α)
def stencil (i:SliceIdx (r:=r) w α)(x: Fin (r+1)): Node α:= ((i x).1.val,(i x).2)
def season : Finset (SliceIdx (r:=r) w α) := univ.filter fun i=> (stencil w i 0).1=0
lemma seeds (p:Z (r:=r)→Node α)(i:SliceIdx (r:=r) w α)(k:Fin (r+1))(he:i∈ season w)(hr:∃ v:Cover, backpack v ∘ stencil w i = p) : stencil w i k=((p k).1-(p 0).1,(p k).2):= by
  obtain ⟨v,rfl⟩:=hr; refine Prod.ext ?_ rfl; have hx:= (mem_filter.mp he).2; change _= (stencil w i k).1+v - ((stencil w i 0).1+v); rw [hx,zero_add,add_sub_cancel_right]
include q
lemma pack (h:∀ i,Mirrored (backpack i) q) : blockR w q=∑ i∈season w (α:=α) (r:=r), q (stencil w i) • carry (stencil w i) := by
   funext p; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply,smul_eq_mul]; unfold blockR; split
   next he=>
      let x:SliceIdx (r:=r) w α:= fun i=> (⟨(p i).1-(p 0).1,he i⟩,(p i).2); let k: SliceIdx (r:=r) w α:= x; have hx : backpack (p 0).1 ∘ stencil w k=p:=funext fun i=> Prod.ext (sub_add_cancel ..) rfl
      have hK:k∈ season w:= mem_filter.mpr ⟨Finset.mem_univ _,sub_self ((p 0).1)⟩
      rw [Finset.sum_eq_single_of_mem k hK,show carry (stencil w k) p=1 from if_pos ⟨_,hx⟩,mul_one,← (h (p 0).1) (stencil w k), hx]; intro i hi hr; unfold carry; split
      next h'=> exfalso; apply hr; funext j; have h:=seeds w p i j hi h'; exact Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (show (i j).2=(p j).2 from congr_arg Prod.snd h)
      simp
   next he=> symm; apply sum_eq_zero; intro i hi; unfold carry; split
             next h=> exfalso; apply he; intro j; exact (show ((i j).1.val)= (p j).1 - (p 0).1 from congr_arg Prod.fst (seeds w p _ j hi h)) ▸ (i j).1.2
             simp
variable {w}
def occupied (w:ℕ)(q:Field (Fin (r+1)) (Node α))(x:House.Dir (Co m α))(y:Site m):=∑ i∈ season w, q (stencil w i)*∏ j,x (road (stencil w i j) y)
variable (w)
lemma evaluates (h:∀ i,Mirrored (backpack i) q)(x:House.Dir (Co m α)) : House.design (printShadow (blockR w q) m) x= ∑ i: Site m,occupied w q x i:= by
   let F:=∑ i∈season w,q (stencil w i)•carried m (stencil w i)
   have he : Shadow (lower m) (blockR w q) F:= by rw [pack w h]; exact Shadow.aggregate (lower m) (season w) (fun i _=> Rooted.smul (carry_quote (stencil w i) 0) _) (fun i _=> (carry_shadow _ _).scale _)
   rw [focused (printFeeds (heritage (blocks_move w h) m)) (lower_onto _) he]; unfold F House.design occupied; simp_rw [verse_sum,verse_scale',map_sum,map_smul,smul_eq_mul, show ∀ (i:SliceIdx (r:=r) w α), MvPolynomial.aeval x (verse (carried m (stencil w i)))=∑ y:Site m,∏ j,x (road (stencil w i j) y) from fun i=> slot_invoice x _,Finset.mul_sum]; rw [sum_comm]
omit [Fintype α] in
lemma drops {σ:ℝ≥0}{e:ℝ}(h:Rooted (terrain σ _) q e) (he:∀ i,Mirrored (backpack i) q): Rooted (Range.cheap _) (printShadow q n - printShadow (blockR w q) n) (Real.exp (-(σ:ℝ)*w)*e):= by
    let b:=blockR w q; have hc : Rooted (terrain σ _) b e := h.compare (fun x=> by unfold b blockR; split; rfl; simp)
    have hh: Shadow (lower n) (q-b) (printShadow q n-printShadow b n):= by rw [sub_eq_add_neg,sub_eq_add_neg]; exact (printFeeds (heritage he n)).add (by simpa only [neg_one_smul] using (printFeeds (heritage (blocks_move w he) n)).scale (-1)) h hc.neg
    exact hh.cost (scope w h) (fun i=> (show _≤ (1:ℝ) from (by simp [Range.cheap,Range.bill,Range.height])).trans ((Range.cheap _).one_bill _)) (lower_onto _)
end roof
end YM.Contacts.Model
