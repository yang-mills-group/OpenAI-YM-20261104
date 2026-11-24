import YM.UVExt.MainCauchy

/-! Loop jet transport uses the full anchor displacement, and directional prices for curls and their one-step differences, before taking the limiting test. The two-leg family's zero moment is applied at each pair of plaquette axes and colors, not to a single slot token. -/

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Laurent Lattice RG Wilson Precision Exterior Bid Matrix Set
open scoped Classical Topology ContDiff BigOperators
variable {G : Gauge} {n : Side} (v : fieldDir G n 1)

private lemma travel_delta (a : TypeFace 2) (t : Walk) (x : Site n) :
    ‖(dColor G n 1 v) (stop x t,a) - dColor G n 1 v (x,a)‖ ≤ (t.length:ℝ)* gradD v := by
  let b (y : Site n) := dColor G n 1 v (y,a)
  have h (y : Site n) (s : Axis) : ‖b (y+step s)-b y‖ ≤ gradD v := by
    change ‖dColor G n 1 v ((y,a).1+step s,(y,a).2)-dColor G n 1 v (y,a)‖ ≤ _
    rw [← delta_entry s v (y,a)]
    exact (norm_le_pi_norm _ _).trans (norm_le_pi_norm (fun s=> deltaV s v) s)
  change ‖b _-b _‖ ≤ _
  induction t generalizing x with
  | nil => simp only [stop,sub_self,norm_zero,List.length_nil,Nat.cast_zero,zero_mul]; exact le_rfl
  | cons d t ih =>
    simp only [stop,List.length_cons,Nat.cast_add,Nat.cast_one]
    have hf : ‖b (x+d.vec)-b x‖ ≤ gradD v := by
      obtain ⟨j,hj|hj⟩:=d
      · exact h x j
      rw [norm_sub_rev]; change ‖b x - b (x + -step j)‖ ≤ _
      nth_rw 1 [show x=x + -step j + step j from Eq.symm (by rw [add_assoc,neg_add_cancel,add_zero])]
      exact h _ _
    exact (norm_sub_le_norm_sub_add_norm_sub _ (b (x+d.vec)) _).trans ((add_le_add (ih _) hf).trans_eq (by ring))

def frozen (b : PlaqAxes) (j : G.ColorIndex) (x : Site n) := part j (dColor G n 1 v (x,plaquette b))
def sent (b : Slot) (j : G.ColorIndex) (x : Site n) := Work.F03.faceCurl (Work.F03.slotFace b x) v j

set_option maxHeartbeats 400000 in
lemma coil_first_bound (x b j) :
    |sent v b j x - frozen v b.plaq j x| ≤ K G*(SlotSize b)*gradD v := by
  have hz := attach_back x b.walk
  rw [add_comm] at hz
  calc
    _ = ‖part j (dColor G n 1 v (stop x b.walk,plaquette b.plaq) - dColor G n 1 v (x,plaquette b.plaq))‖ := by rw [map_sub,Real.norm_eq_abs,hz]; rfl
    _ ≤ ‖part j‖ * ((b.walk.length:ℝ)*gradD v) := (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_left (travel_delta ..) (norm_nonneg _))
    _ ≤ _ := by unfold SlotSize Slot.length; unfold gradD; rw [← mul_assoc]; gcongr <;> first|exact part_price j|positivity [K_pos G]|exact_mod_cast Nat.le_add_right _ 4

lemma sent_price (x b j) : |sent v b j x| ≤ K G*‖dColor G n 1 v‖ := by
   change ‖part j (dColor G n 1 v (_, _))‖ ≤ _
   exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul ((part_price ..)) (norm_le_pi_norm _ _) (norm_nonneg _) (zero_le_one.trans (K_pos G)))
lemma frozen_price (x b j) : |frozen v b j x| ≤ K G*‖dColor G n 1 v‖ := by
   change ‖part j (dColor G n 1 v _)‖ ≤ _
   exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul ((part_price ..)) (norm_le_pi_norm _ _) (norm_nonneg _) (zero_le_one.trans (K_pos G)))

lemma stream_two (A : Token G 2) x : stream v x A=sprout v x (A.1 0) (A.2 0) * sprout v x (A.1 1) (A.2 1) := by unfold stream; rw [Fin.prod_univ_two]
lemma coil_rates (x : Site n) (A : Token G 2) :
     (∀ j<2, tag j (stream v x A)=0) ∧
     tag 2 (stream v x A) = 2*∏ i, sent v (A.1 i) (A.2 i) x := by
   rw [stream_two]
   have h i := (sprout_bill v x (A.1 i) (A.2 i) (SlotSize (A.1 i)) le_rfl).1
   constructor
   · exact ((h 0).multiply (h 1)).vanish
   unfold tag
   rw [iteratedDeriv_mul ((h 0).smooth.of_le (m:=(2:ℕ)) (by simp)) ((h 1).smooth.of_le (m:=(2:ℕ)) (by simp))]
   norm_num [Finset.sum_range_succ, sprout_zero, sprout_first,sent, Fin.prod_univ_two]; ring

private lemma carries_summable {ι : Type*} {W : ι→ℝ} {σ C : ℝ} {n : ι→ℝ} (h : Carries C σ n W) (hs : 0<σ) : Summable (fun i=>‖W i‖) :=
   Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hs.le (h.1 i)))) h.paid.2.1

private lemma bounded_product {ι ι' : Type*} (y : ι'→ℝ) (z : ι→ι') {f : ι→ℝ} {C : ℝ} (hw : ∀ i,‖y i‖ ≤ C) (hg : Summable (fun i=>‖f i‖)) : Summable (fun i=>f i • y (z i)) :=
   Summable.of_norm_bounded (g:=fun i=> ‖f i‖ * C) (f:=fun i=>f i • y (z i)) (hg.mul_right C) fun i=>(norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _))

private lemma pool_funds {V : ℕ→RG.Atom G 2}
    (he : ∀ p : Fin 2→PlaqAxes,∀ b : Fin 2→G.ColorIndex, HasSum (fun i:ℕ=>if (fun l=>((V i).leg l).plaq)=p then (V i).coeff b else 0) 0)
    (hs : Summable (fun i : ℕ × (Fin 2→G.ColorIndex)=>‖(V i.1).coeff i.2‖)) (j : (Fin 2→PlaqAxes) × (Fin 2→G.ColorIndex)) : pool (fun i : ℕ × (Fin 2→G.ColorIndex)=> (V i.1).coeff i.2) (fun i=>((fun l=>((V i.1).leg l).plaq),i.2)) j=0 := by
   let f (i : ℕ × (Fin 2→G.ColorIndex)) := (V i.1).coeff i.2
   let b := Fin 2→G.ColorIndex; let τ := (Fin 2→PlaqAxes) × b
   let p (i : ℕ × b) : τ := ((fun l=>((V i.1).leg l).plaq),i.2)
   change pool f p j=0
   have ho : pool f p j=∑' i, if p i=j then f i else 0 := (pool_mask (f:=f) _ _).trans <| tsum_congr fun x=>by by_cases he:p x=j <;> simp only [he,↓reduceIte]
   have ht : Summable (fun i=> if p i=j then f i else 0) := Summable.of_norm_bounded hs (fun i=>by split <;> simp [f])
   rw [ho,ht.tsum_prod]
   calc
     _ = ∑' i : ℕ, if (fun l=>(V i).leg l |>.plaq)=j.1 then (V i).coeff j.2 else 0 := tsum_congr fun i=> ?_
     _ = 0 := by convert (he j.1 j.2).tsum_eq using 1
   rw [tsum_fintype]; change (∑ k : b, if p (i,k)=j then f (i,k) else 0)=_
   rw [Finset.sum_eq_single_of_mem j.2 (Finset.mem_univ _)]
   · change (if (((fun l=>(V i).leg l |>.plaq),j.2):τ)=j then f _ else 0)=_; exact ite_congr (by obtain ⟨a,b⟩:=j; simp) (fun _=>rfl) (fun _=>rfl)
   rintro k _ hne; exact if_neg (fun hh => hne (congr_arg (Prod.snd (α:=Fin 2→PlaqAxes)) hh))
set_option maxHeartbeats 600000 in
lemma twin_freeze (x : Site n) {s C : ℝ} {V : ℕ→RG.Atom G 2} {w : Token G 2→ℝ} (hW : w=necklace V)
    (hs : 0<s) (hm : SumBudget (fun i=> (V i).budget s) C)
    (he : ∀ p : Fin 2→PlaqAxes,∀ b : Fin 2→G.ColorIndex, HasSum (fun i:ℕ=>if (fun l=>((V i).leg l).plaq)=p then (V i).coeff b else 0) 0) :
    tag 2 (song v x w) = 2*(∑' (A : Token G 2), w A * ((∏ i, sent v (A.1 i) (A.2 i) x) - (∏ i, frozen v (A.1 i).plaq (A.2 i) x))) := by
  classical
  let τ := (Fin 2→PlaqAxes) × (Fin 2→G.ColorIndex)
  let place (z : ℕ × (Fin 2→G.ColorIndex)) : Token G 2 := ((V z.1).leg,z.2)
  let unplace : Token G 2→τ := fun i=>((fun l=>(i.1 l).plaq),i.2)
  let f (i : ℕ × (Fin 2→G.ColorIndex)) := (V i.1).coeff i.2
  let b := Fin 2→G.ColorIndex
  have hw : w=pool f place := hW
  have hw' : Carries C s breath w := (hw.symm ▸ necklaces_paid V s C hm hs)
  let B (R : τ) := ∏ i, frozen v (R.1 i) (R.2 i) x
  let Y (R : Token G 2) := ∏ i, sent v (R.1 i) (R.2 i) x
  have hb : Carries C s (fun i : ℕ×b=> ((V i.1).length:ℝ)) f := product_money (σ:=s) (C:=C) (fun i:ℕ=>((V i).length:ℝ)) (fun _=>by positivity) (fun j=>(V j).magnitude) (fun i=>rfl) hm
  have hc (p : Token G 2) : |Y p| ≤ (K G*‖dColor G n 1 v‖)^2 := (by unfold Y; rw [Fin.prod_univ_two,abs_mul,pow_two]; exact mul_le_mul (sent_price ..) (sent_price ..) (abs_nonneg _) (by positivity [K_pos G]))
  have hh (p : τ) : |B p| ≤ (K G*‖dColor G n 1 v‖)^2 := (by unfold B; rw [Fin.prod_univ_two,abs_mul,pow_two]; exact mul_le_mul (frozen_price ..) (frozen_price ..) (abs_nonneg _) (by positivity [K_pos G]))
  have HG := carries_summable hb hs
  have hY (j : τ) : pool f (unplace ∘ place) j = 0 := by exact pool_funds he HG _
  have hQ := (pool_read (Y:=ℝ) f Y place HG.of_norm (bounded_product _ _ hc HG))
  have hR := (pool_read f (B ∘ unplace) place HG.of_norm (bounded_product _ _ (fun p=>hh (unplace p)) HG))
  have hZ := (pool_read f B (unplace ∘ place) HG.of_norm (bounded_product _ _ hh HG)).tsum_eq.symm
  have hV := hQ.sub hR |>.tsum_eq
  change (∑' z,(pool f place z * Y z - pool f place z * B (unplace z)))=(∑' z,f z*Y (place z))-∑' z,f z*B (unplace (place z)) at hV
  rw [←hw] at hV; simp_rw [← mul_sub] at hV
  change (∑' z,f z*B (unplace (place z)))=∑' j,pool f (unplace∘place) j*B j at hZ
  simp_rw [hY,zero_mul,tsum_zero] at hZ
  change _ = 2*∑' z, w z*(Y z-B (unplace z))
  rw [hV,hZ,sub_zero, ← (show (∑' j:Token G 2,pool f place j * Y j)=_ from (show (_=∑' z:ℕ×b,f z*Y (place z)) from hQ.tsum_eq)), ←tsum_mul_left,←hw]
  have he := (song_sum v hw' hs x 2 0).tsum_eq.symm
  change tag 2 _= _
  exact he.trans (tsum_congr fun i=> by rw [show iteratedDeriv 2 (stream v x i) 0 = _ from (coil_rates v x i).2]; exact mul_left_comm _ _ _)
lemma tag_spiral {Z : Shadow G} {p C σ : ℝ} (h : PaidShadow Z p C σ) (ht : 0 < σ) q : tag q (spiral Z v) = ((Fintype.card Signed:ℝ)⁻¹) * ∑ s:Signed,∑ x:Site n, tag q (song (pulled v s) x Z.loop) := by
  unfold spiral; have hx (s) := flow_sum (ι:=Site n) fun x=>song_smooth (pulled v s) h.coeffTwo ht x
  rw [tag_smul _ (flow_sum hx),tag_sum _ hx]
  exact congr_arg ((Fintype.card Signed:ℝ)⁻¹ * ·) (Finset.sum_congr rfl fun s _=>tag_sum _ (fun x=>song_smooth (pulled v s) h.coeffTwo ht x))

end YM.UVExt.Paths
