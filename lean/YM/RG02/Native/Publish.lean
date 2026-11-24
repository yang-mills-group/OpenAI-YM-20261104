import YM.RG02.Native.Frame

/-!
# Rooted publication by coherence and budgets

Fatou via writing canonical stalls of all entries. DCT true period. Uses a
summability bound at κ>0 ALREADY bought on periodic kernels sized at this
arity. `proper` only analytic finite colors, no topology on α, all estimates
in physical stride w. No multiplying by native volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Filter Set Metric Finset Lattice RG Precision Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology
variable {α β A Z: Type}{m n:Side}
variable [NormedAddCommGroup Z] [Fintype A] [Fintype α]

def stalls (F:OnTorus α β A Z n) : CoverForm α β A Z:=fun i v=> if stall (0:Site n) (emit 0 v)=v then F (0,i) (emit 0 v) else 0
omit [Fintype α] in
lemma stamps (F:OnTorus α β A Z n)(i:β)(v:A→Leaf α n): stalls F i (stall 0 v)=F (0,i) v:=by rw [stalls,emit_stall,if_pos rfl]
lemma quiet (F:OnTorus α β A Z n)(i:β)(v:A→Arm α)(h:v∉Finset.univ.image (stall (0:Site n))) : stalls F i v=0:=by
   unfold stalls; rw [if_neg]; intro he; exact h (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,he⟩)

lemma narrow_stalls (F:OnTorus α β A Z n)(a C:ℝ)(h:∀ i:Leaf β n,ticket F a i≤C) : narrow a C (stalls F):=by
   intro i
   let s:=Finset.univ.image (stall (A:=A) (α:=α) (0: Site n))
   let f:= fee a (stalls F) i
   have hh v (h:v∉s): f v=0:=by simp [f,fee,quiet F i v h]
   refine ⟨fun v=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _), summable_of_ne_finset_zero hh, ?_⟩
   change (∑' v,f v)≤_
   rw [tsum_eq_sum hh, show s=_ from rfl,Finset.sum_image (stall_one (A:=A) (α:=α) (_:Site n)).injOn]
   unfold f fee; simp_rw [stamps,exact_stall]; apply h (0,i)

-- preserve exact projection to eligible division
lemma imprint_stalls (U:PeriodicTable α β A Z) {t:ℕ}(hc:coherent t U)(h:divides n m)(hp:t≤n.val): imprint (stalls (U m)) n=U n:=by
    funext i j; unfold imprint
    have hz : i=collapse h i.1 (0,i.2):= Prod.ext (by simp [collapse, lieBy]) rfl
    have hh (k:A→Leaf α m): collapse (α:=α) h i.1 ∘ k=emit i.1 (stall (0:Site m) k) := by
       have he:= collapse_emit (A:=A) h i.1 (0:Site m) (stall (0:Site m) k); rw [emit_stall] at he; simpa [lieBy] using he
    conv_rhs=> rw [hz,hc n m h i.1 (0,i.2) j hp]
    rw [tsum_eq_sum (s:=Finset.univ.image (stall (A:=A) (α:=α) (0:Site m))),Finset.sum_image (stall_one (A:=A) (α:=α) (_:Site m)).injOn]
    · apply Finset.sum_congr rfl; intro x _
      -- casts hz performed just RHS i; compare
      rw [stamps,hh]; split_ifs <;> rfl
    intro a ha; split; exact quiet _ _ _ ha; exact rfl -- edit

private lemma chips (w:ℝ)(h:0<w): Summable fun x:Cover=>Real.exp (-w*Laurent.stride x):=by
    let d:= (Fintype.card Axis :ℝ); have hd : 0<d:= by unfold d; positivity
    apply Summable.of_nonneg_of_le (fun p=> (Real.exp_pos _).le) ?_ (YM.Laurent.Width.compactPay (α:=Axis) (w/d) (by positivity)).2.1
    intro z; apply Real.exp_le_exp.mpr
    have hh : YM.Laurent.size z ≤ Fintype.card Axis * Laurent.stride z:= by
       apply le_trans (b:=∑ _ : Axis,Laurent.stride z); exact Finset.sum_le_sum fun i _=> Finset.le_sup (f:=fun j=>Int.natAbs (z j)) (Finset.mem_univ i); simp
    have hk : (YM.Laurent.size z:ℝ)≤ d * Laurent.stride z:=by unfold d; exact_mod_cast hh
    rw [neg_mul,neg_mul,neg_le_neg_iff,div_mul_eq_mul_div, div_le_iff₀ hd]; calc
      _ ≤ w* (d* Laurent.stride z):= mul_le_mul_of_nonneg_left hk h.le
      _ = _:=by ring

lemma chipBank (w : ℝ)(h:0<w): Summable fun x:A→Arm α=> Real.exp (-w* length x):=by
    let f (u:Cover):=Real.exp (-w*Laurent.stride u)
    have hx : Summable f:=chips w h
    -- include colors
    have he : Summable (f ∘ Prod.fst (β:=α)):= by
       have hh : Summable (fun i:Cover×α=> ‖f i.1 * (fun _ : α=>(1:ℝ)) i.2‖):= hx.norm.mul_norm (Summable.of_finite (f:=norm ∘ fun _ : α=>(1:ℝ)))
       apply hh.congr; intro i; simp [f]
    apply (Laurent.cross (V:=A) (X:=fun _=>Arm α) (f:=fun _=> f ∘ Prod.fst) (fun _=>he.norm)).2.summable.congr
    intro i; simp only [length,Nat.cast_sum,Finset.mul_sum,Real.exp_sum]; rfl

omit [Fintype α] in
private lemma decays {w C : ℝ}{F:CoverForm α β A Z}(h:narrow w C F)(i:β)(x:A→Arm α) : ‖F i x‖≤C *Real.exp (-w * length x):=by
    have hh:= (((h i).2.1).le_tsum x (fun j _ =>(h i).1 _)).trans (h i).2.2
    unfold fee at hh
    rw [neg_mul,Real.exp_neg,← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),mul_comm]; exact hh

section collect
variable [Fintype β] [ProperSpace Z]
private def Continent (t :ℕ)(k :ℕ):Side:=⟨(k+t+1).factorial,Nat.factorial_pos _⟩
private lemma first (t k:ℕ) : k+t ≤ (Continent t k).val:= by
    exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_dvd (Continent t k).pos (Nat.dvd_factorial (by omega) (by omega : k+t+1 ≤ k+t+1)))
private lemma continents (t:ℕ)(n:Side) : ∀ᶠ i:ℕ in atTop, divides n (Continent t i):=by
    filter_upwards [eventually_ge_atTop n.val] with k hk; exact Nat.dvd_factorial n.pos (by omega)

-- compactness on the cover. use locally bounded frame if the vertex
-- is analytic at all finite periods. finite t; no phase transfer.
theorem publish {U:PeriodicTable α β A Z}{t:ℕ}{w C:ℝ}(hw:0<w)(hb:0≤C)(he:charged t w C U)(hc:coherent t U) :
    ∃ F:CoverForm α β A Z,narrow w C F ∧ ∀ n:Side,t≤n.val → U n= imprint F n:=by
    let F := fun i => stalls (U (Continent t i))
    have hf i : narrow w C (F i):= narrow_stalls _ w _ (he _ (le_trans (by omega) (first t i)))
    let D := fun v:A→Arm α=> C * Real.exp (-w * length v)
    have hu: Summable D:= (chipBank w hw).mul_left _
    let s : Set (CoverForm α β A Z) := {g | ∀ i, g i ∈ ({f : (A→Arm α)→Z | ∀ j, f j∈Metric.closedBall 0 (D j)})}
    have hg : IsCompact s:= isCompact_pi_infinite fun _=> isCompact_pi_infinite fun _=> isCompact_closedBall _ _
    obtain ⟨G,_,u,hs,hg⟩:=hg.tendsto_subseq (show ∀ i:ℕ,F i ∈ s from fun i j k=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact decays (hf i) j k))
    have hq (i:β)(v:A→Arm α) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg i) v
    refine ⟨G,fun i=> ?_,fun n hn=> ?_⟩
    · let f:= fee w G i; have h0 j : 0 ≤ f j := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      have hh(s:Finset (A→Arm α)): ∑ j∈s,f j ≤ C:= by
         apply le_of_tendsto' (f:=fun k=> ∑ j∈s,fee w (F (u k)) i j) (tendsto_finsetSum _ fun j _=> tendsto_const_nhds.mul ((hq i j).norm))
         intro b; exact (((hf _ i).2.1).sum_le_tsum s (fun v _=>(hf _ i).1 _)).trans (hf _ i).2.2
      have hz:= summable_of_sum_le h0 hh
      exact ⟨h0,hz,hz.tsum_le_of_sum_le hh⟩
    funext i j
    let p (k:ℕ)(v:A→Arm α):= if emit i.1 v=j then F (u k) i.2 v else 0
    let q(v:A→Arm α):= if emit i.1 v=j then G i.2 v else 0
    have hy : Tendsto (fun k:ℕ=> ∑' v:A→Arm α,p k v) atTop (𝓝 (∑' v:A→Arm α,q v)):=by
       have h' k v : ‖p k v‖≤D v:=by unfold p; split; exact decays (hf _) _ _; simp; unfold D; positivity
       apply tendsto_tsum_of_dominated_convergence hu _ (Eventually.of_forall h')
       intro v; unfold p q; by_cases hq':emit i.1 v=j; simp_rw [if_pos hq']; exact hq i.2 v; simp_rw [if_neg hq']; exact tendsto_const_nhds
    have hx : imprint G n i j=∑' v,q v:= by unfold imprint; apply tsum_congr; intro v; unfold q; split_ifs <;> rfl
    rw [hx]; apply tendsto_nhds_unique _ hy
    apply (tendsto_const_nhds (x:=U n i j)).congr'
    filter_upwards [hs.tendsto_atTop.eventually (continents t n)] with k hk
    rw [← imprint_stalls U hc hk hn]; unfold imprint; apply tsum_congr; intro k; unfold p; split_ifs <;> rfl
end collect

-- uniqueness independent of precision or plate
section uniqueness
variable [CompleteSpace Z]
omit [Fintype α] in
theorem narrow.limit {v:ℝ}{F:CoverForm α β A Z}(n:ℕ→Side)(hf:Tendsto (fun i:ℕ=> (n i).val) atTop atTop){C:ℝ}(h:narrow v C F)(hp:0 ≤ v) (j:β)(k:A→Arm α) :
    Tendsto (fun i=> imprint F (n i) (0,j) (emit 0 k)) atTop (𝓝 (F j k)):=by
    let f(x:A→Arm α):= if x=k then F j k else 0
    let g(i:ℕ)(x:A→Arm α) := if emit (0:Site (n i)) x=emit (0:Site (n i)) k then F j x else 0
    have he : (∑' x,f x)= F j k:=by exact tsum_eq_single k (fun _ hx=> if_neg hx)|>.trans (if_pos rfl)
    have hc : Tendsto (fun i:ℕ=>∑' x,g i x) atTop (𝓝 (∑' x,f x)):=by
       have hs := narrow_mono h hp le_rfl j
       have h₀ i x : ‖g i x‖ ≤ fee 0 F j x := by unfold g; split; simp [fee]; rw [norm_zero]; exact hs.1 x
       apply tendsto_tsum_of_dominated_convergence hs.2.1 ?_ (Eventually.of_forall h₀)
       intro x; apply (tendsto_const_nhds (x:=f x)).congr'
       filter_upwards [hf.eventually (eventually_gt_atTop (2* length k)), hf.eventually (eventually_gt_atTop (2* length x))] with q hq hs
       unfold f g; by_cases h:x=k; · simp [h]
       rw [if_neg h,if_neg]; intro H; apply h
       calc
          _ = stall (0:Site (n q)) (emit 0 x):=(unchanged 0 _ hs).symm
          _ = _ := by rw [H,unchanged 0 _ hq]
    rw [he] at hc
    apply hc.congr; intro i; unfold imprint; apply tsum_congr; intro z; unfold g; change (if _ then _ else _)=_; split_ifs <;> rfl

omit [Fintype α] in
lemma same {F G:CoverForm α β A Z}{v C w D:ℝ}(h:narrow v C F)(hl:narrow w D G)(hv:0≤v)(hw:0≤w) {t:ℕ}(hq:∀ n:Side,t≤n.val→ imprint F n=imprint G n) : F=G:=by
    let n:= Continent t
    have hh : Tendsto (fun i:ℕ=>(n i).val) atTop atTop:=tendsto_atTop_atTop.mpr (fun i=> ⟨i,fun j hj=> le_trans (by omega) (first t j)⟩)
    funext j k; apply tendsto_nhds_unique (h.limit n hh hv j k); apply (hl.limit n hh hw j k).congr; intro i; rw [hq (n i) (le_trans (by omega) (first t i))]
end uniqueness
end YM.RG02.Native
