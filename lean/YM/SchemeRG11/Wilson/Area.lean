import YM.SchemeRG11.Wilson.Mire
/-! Rank-4 shelling. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I J E:Type*} [NormedAddCommGroup E] {N:Side}

def price (L:I→ℕ)(X:ℝ): Prop:=∀ s :Finset I,∀ {k:ℕ}, k>0→(∀ i∈s,L i≤k)→(s.card:ℝ)≤X*(k:ℝ)^4
lemma whorl {f:I→E}{A:I→ℕ}{X C:ℝ}(hx:price A X)(hX:0≤X)(hC:0≤C) (k:ℕ)(hk:0<k)(s:Finset I)(hs:∀ i∈s,k < A i)(he:∀ i∈s,‖f i‖ * (A i:ℝ)^6 ≤ C) :
  (∑ i∈s,‖f i‖) ≤ X*32*C/(k:ℝ)^2:=by
 have H (n:ℕ)(k:ℕ)(hk:0<k) (s:Finset I)(hs:∀ i∈s, k<A i)(he:∀ i∈s,‖f i‖ * (A i:ℝ)^6≤C)(hi:∀ i∈s,A i≤2^n*k) : (∑ i∈s,‖f i‖) ≤ X*32*C/(k:ℝ)^2:=by
   induction n generalizing k s with
   | zero=>
     have hb:s=∅:=Finset.not_nonempty_iff_eq_empty.mp (fun ⟨i,h⟩=> (by have hv:=hi i h; norm_num at hv; exact (not_lt.mpr hv) (hs _ h)))
     rw [hb,Finset.sum_empty]; positivity
   | succ n IH=>
     let v:=s.filter fun i=> A i≤ 2*k; let p:=s\v
     have hv:=Finset.filter_subset (p:=fun i=> A i≤ 2*k) (s:=s)
     have hi' :∀ i∈v,A i≤2*k:=fun i h=>(Finset.mem_filter.mp h).2
     rw [← Finset.sum_sdiff hv]
     have hm:= IH (2*k) (by omega) p (fun i h=> by obtain ⟨h₁,h₂⟩:=Finset.mem_sdiff.mp h; exact lt_of_not_ge fun hh=>h₂ (Finset.mem_filter.mpr ⟨h₁,hh⟩)) (fun i h=> he i (Finset.mem_sdiff.mp h).1) (fun i h=> (hi i (Finset.mem_sdiff.mp h).1).trans (le_of_eq (by ring)))
     change (∑ i∈p,‖f i‖) + (∑ i∈v,‖f i‖) ≤ _
     have hr:0<(k:ℝ):=by exact_mod_cast hk
     apply le_trans (add_le_add hm (show (∑ i∈v, ‖f i‖)≤ X*((2*k:ℕ):ℝ)^4*(C/(k:ℝ)^6) from ?_))
     · push_cast; field_simp; nlinarith only [mul_nonneg hC hX]
     apply le_trans (b:=∑ _∈v,C/(k:ℝ)^6) (Finset.sum_le_sum (fun i hj=> ?_))
     · rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hx v (by omega) hi') (by positivity)
     have ht: (k:ℝ) < (A i:ℝ) := by exact_mod_cast hs i (hv hj)
     have hp:= he i (hv hj); rw [le_div_iff₀ (by positivity)]; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le ht.le _) (norm_nonneg _)).trans hp
 obtain ⟨n,hn⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (r:=(2:ℕ)) (by decide)).eventually (eventually_gt_atTop (s.sup A))).exists
 apply H n k hk s hs he ; intro i hi; exact (Finset.le_sup hi).trans (le_trans hn.le (le_mul_of_one_le_right (Nat.zero_le _) (show 1≤k from hk)))
lemma boxCost(k:ℕ): (box k).card ≤ (2*k+1)^4:=by
 let v:=Finset.Icc (-(k:ℤ)) (k:ℤ)
 calc _ ≤ (Fintype.piFinset (fun _:Axis=>v)).card:=by
        refine Finset.card_le_card fun i hi => Fintype.mem_piFinset.mpr fun a=> Finset.mem_Icc.mpr ⟨(box_test.mp hi).1 a,(box_test.mp hi).2 a⟩
      _ = _:=by simp [Axis,v,Int.card_Icc,Fintype.card_piFinset]; omega -- inspect
lemma coverage : price diam 81:=by
 intro s k hk h
 have he1 : (s.card:ℝ) ≤ ((2*k+1:ℕ):ℝ)^4 := by exact_mod_cast (Finset.card_le_card (show s⊆ box k from fun w hw=> wrapcost w (h _ hw))).trans (boxCost k)
 apply he1.trans; rw [show 81*(k:ℝ)^4=(3*(k:ℝ))^4 from by ring]; gcongr; exact_mod_cast (show 2*k+1≤3*k by omega)

def orbitRank(n:Side)(o:Site n)(i j:Axis)(x: Site n): ℕ:= min (pdist (x-o)) (pdist (mirror i j x-o))
lemma places(o: Site N)(i j:Axis) : price (orbitRank N o i j) 162:=by
 intro s k hk h; let V:= Band.inside N k
 have he:(V.card:ℝ) ≤ (3*(k:ℝ))^4:=(by refine le_trans (b:=(((2*k+1:ℕ):ℝ))^4) ?_ ?_; exact_mod_cast Band.inside_count k (n:=N); gcongr; exact_mod_cast (show 2*k+1≤3*k by omega))
 have hj(a:Site N)(ha:a∈s):pdist (a-o)≤k ∨ pdist (mirror i j a-o)≤ k:=min_le_iff.mp (h _ ha)
 let g(x:Site N):=x+o; let w:=mirror i j (N:=N)
 have hu:s⊆V.image g ∪ V.image (w ∘ g):= fun a ha=> by
   rcases hj a ha with H|H
   · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a-o, Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩, sub_add_cancel ..⟩)
   exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w a-o,Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩,by unfold w g; simp only [comp_apply,sub_add_cancel]; apply mirror_inv⟩)
 apply le_trans (show (s.card:ℝ)≤ V.card+(V.card:ℝ) by exact_mod_cast Finset.card_le_card hu |>.trans ((Finset.card_union_le ..).trans (add_le_add Finset.card_image_le Finset.card_image_le)))
 linarith only [he]
end YM.SchemeRG11.Acorn
