import YM.UVExt.FoldFaces

/-! Intertwine the installed column with pullback (same block factor, no change of map at any of the larger periods compared). The price used globally is absolute summability on the cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Covering
open Lattice Laurent Bid RG Precision Wilson Exterior Matrix Set Function Filter Bloch
open scoped Classical ContDiff Topology BigOperators
variable {G : Gauge} {T : Schedule} {A : Levels G} {s t : ℕ} {n m : Side} (j : ℕ)
def groups (T:Schedule) (u : (T.period s).val ∣ (T.period t).val) : Tiles (T.side j s) (T.side j t) := ⟨Nat.mul_dvd_mul_right u _⟩
variable (u : (T.period s).val ∣ (T.period t).val) (g : ℕ→ℕ)
lemma parent_compatible (x : Site (T.side (j+1) t)) : (groups (j+1) T u).quot ((T.oneStep j t).embed ((T.oneStep j t).parent x)) =
    (T.oneStep j s).embed ((groups j T u).quot ((T.oneStep j t).parent x)) := by
     let y := lift ((T.oneStep j t).parent x)
     rw [show (T.oneStep j t).parent x=wrap (T.side j t) y from (wrap_lift _).symm, fold_wrap, Ratio.embed_wrap,Ratio.embed_wrap,fold_wrap]; rfl
lemma reciprocal_square (x : Site (T.side (j+1) t)) : (T.oneStep j s).splitSites ((groups (j+1) T u).quot x) =
    ((groups j T u).quot ((T.oneStep j t).parent x), (T.oneStep j t).residue x) := by
   let q := T.oneStep j t; let r := T.oneStep j s; let h i := groups i T u
   suffices r.assemble ((h j).quot (q.parent x), q.residue x) = (h (j+1)).quot x from by change r.splitSites (_)=_; rw [←this]; exact r.splitSites.apply_symm_apply _
   change (r.assemble _ = (h (j+1)).quot x)
   have ht : (h (j+1)).quot (wrap (T.side (j+1) t) (lift (q.residue x))) = wrap (T.side (j+1) s) (lift (q.residue x)) := fold_wrap _ _
   calc
     r.assemble _ = (h (j+1)).quot (q.embed (q.parent x)) + (h (j+1)).quot (wrap (T.side (j+1) t) (lift (q.residue x))) := congr_arg₂ (fun (i j:Site (T.side (j+1) s))=>i+j) (parent_compatible j u x).symm ht.symm -- orientation parent opposite!
     _ = _ := (map_add _ _ _).symm.trans (congr_arg _ (q.unpack_at x))

lemma cursor (n : Side) {α β : Type*} [Fintype β] (A : Row α β) (ht : ∀ a b,Summable fun i=> ‖A a b i‖) (v : Site n×β→ℝ) (u : Site n × α) :
    (A.acts n *ᵥ v) u = ∑ b:β,∑' i, A u.2 b i * v (u.1 + wrap n i,b) := by
    classical
    simp only [mulVec,dotProduct, Fintype.sum_prod_type]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _=> ?_
    let f (x : Site n) (i : Cover) := if x = u.1+wrap n i then A u.2 t i else 0
    have hS x : Summable (f x) := Summable.of_norm_bounded (ht u.2 t) (fun i=>by unfold f; split <;> simp)
    have he (x : Site n) : A.acts n u (x,t) =∑' i:Cover,f x i := by exact tsum_congr (fun i : Cover=> by
       change (if (x,t).1=u.1+_ then _ else _)=_; by_cases he:x=u.1+wrap n i <;> simp_all [f])
    simp_rw [he]
    change (∑ x : Site n,(∑' i : Cover,f x i)*v (x,t))= _
    simp_rw [← tsum_mul_right]; rw [← Summable.tsum_finsetSum (fun (i : Site n) (_ : i∈(Finset.univ:Finset _))=> (hS i).mul_right (v (i,t)))]
    apply tsum_congr; intro i
    change (∑ x:Site n,f x i*v (x,t))= _
    rw [Finset.sum_eq_single (u.1+wrap n i) (by intro; intros; unfold f; simp_all) (by simp)]; unfold f; rw [if_pos rfl]

lemma install_formula {c f : Side} (Q : Ratio c f) (N : Cross Q.count (TypeFace 1) (TypeFace 1)) (ht : ∀ a b,Summable (‖N a b ·‖)) (v : Body 1 c → ℝ) :
   installed Q N *ᵥ v = fun i:Body 1 f=>∑ k:TypeFace 1,∑' q:Cover, N (Q.residue i.1,i.2) k q * v (Q.parent i.1 + wrap _ q,k) := by
    funext i; unfold installed; rw [show (Matrix.submatrix _ _ _) *ᵥ v = fun t=> ((N.acts c)*ᵥ v) (splitCo Q (TypeFace 1) t) from funext fun _=>rfl]; change ((N.acts c *ᵥ v) ((splitCo ..) i))=_; rw [cursor c N ht,split_co]

variable {X : ∀ i, Transfers A i} {P : MapPrices} {M : Horizon A} (h : Discipline P A M) {u' : ℕ→ℕ} (hg : Tendsto u' atTop atTop) (hX : Follows A u' M X)
include h hX hg
lemma label_budgets (m z j) : Summable fun i => ‖X m z j i‖ := by
    let s := P.α (A.clock.J (m+1)); let C := P.Ω (A.clock.J (m+1)) / (A.S.block m).val
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (Next.Free.UV.flot_summable (σ:=s) (D:=C) (by unfold s; exact P.alpha_pos ..))
    intro i; apply le_of_tendsto ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hX.entries m) z) j) i).norm)
    filter_upwards [Tendsto.eventually hg (eventually_gt_atTop m)] with k H; apply Next.Free.UV.width_flot _ z j i
    have ht := ((h.plan.costs (u' k) m (by exact H)).2.2.2 [] (Nat.zero_le _) |>.1); simp only [advanceC,List.length_nil,add_zero,pow_one] at ht; exact ht -- factor ^1 mismatch

variable {u₀ t₀ : ℕ} (haux : (A.S.period u₀).val ∣ (A.S.period t₀).val)
lemma across_towers (b : Dir G (A.S.side j u₀)) :
    (groups (j+1) A.S haux).clone (mapBind A M X j u₀ b)=mapBind A M X j t₀ ((groups j A.S haux).clone b) := by
    let l := A.S.oneStep j t₀; let r := A.S.oneStep j u₀; let hR m := groups m A.S haux
    change (hR (j+1)).clone (polish (installed r (X j)) b) = polish (installed l (X j)) ((hR j).clone b)
    ext x i
    let v j := parts G 1 b j
    change (installed r (X j) *ᵥ v i) ((hR (j+1)).quot x.1,x.2) = (installed l (X j) *ᵥ _) x
    rw [install_formula r (X j) (label_budgets h hg hX j),install_formula l (X j) (label_budgets h hg hX j)]
    have hh := reciprocal_square j haux x.1
    let z' := (hR (j+1)).quot x.1
    have hh := (r.unpack z').trans hh
    have hr := hh
    change ((_ : Site (A.S.side _ _)),(_ : Site (A.S.block j))) = _ at hh -- annot
    have hr₁ : _ := congr_arg (fun y' : Site (A.S.side j u₀) × Site (A.S.block j)=>y'.1) hh
    have hr₂ : _ := congr_arg (fun y' : Site (A.S.side j u₀) × Site (A.S.block j)=>y'.2) hh
    clear hh hr; have hh := And.intro hr₁ hr₂
    change r.parent ((hR (j+1)).quot x.1) = _ ∧ r.residue _=_ at hh
    dsimp only [Function.comp_apply]; simp only [hh.1]; unfold parts; apply Finset.sum_congr rfl; intro a _; apply tsum_congr; intro k
    dsimp only [Tiles.clone, v]
    change _=(_ * b ((hR j).quot (_+wrap _ k),a) i)
    rw [map_add,fold_wrap]
    have hk : X j ((r.residue z' : Site (A.S.block j)),x.2) a k =  X j (l.residue x.1,x.2) a k := congr_arg (fun t=> X j (t,x.2) a k) (hh.2 : r.residue z' = l.residue x.1)
    exact congr_arg₂ (· * ·) hk rfl

lemma quota_step : quota (groups (j+1) A.S haux)=quota (groups j A.S haux) := by
    let L := A.S.block j
    unfold quota Schedule.side Schedule.denominator
    simp only [PNat.mul_coe,Nat.cast_mul]; have hx : ((A.S.block j).val:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (A.S.block j).property)
    congr 1 <;> field_simp [hx] <;> ring -- denominators

end YM.UVExt.Paths.Covering
