import YM.UVExt.DualTiles
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Precision RG Lattice Wilson Matrix Laurent Tree Bloch Exterior Bid Tensor Set Function Next.Free
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {N:Supply.Rolls s} {Q : PostCost N} {H : ChartRatio G} (K : Kin M H)
    (h : Discipline P A M) (hk : K.Planned Q) (u : ℕ→ℕ) (hu : Tendsto u atTop atTop) (v : ℕ→ℕ) (hv : Tendsto v atTop atTop)
    {U V : ℕ→Shadow G} (hU : ∀ m, woodPassing K u m U) (hV : ∀ m,woodPassing K v m V)
    {X : (i:ℕ)→Transfers A i} (hX : Follows A u M X)
    {x y : ℕ→ℝ} (hp : ∀ i,Tendsto (fun j=>K.alpha (u j) i) atTop (𝓝 (x i))) (hp' : ∀ i,Tendsto (fun j=>K.alpha (v j) i) atTop (𝓝 (y i))) (hN : LocalRatio H)
    (hh : ∀ d,confluent K u v 4 d)
def divisibility (T : Schedule) := ∀ c:Side,∀ z,∃ p≥z,c.val ∣ (T.period p).val
variable (hG : Nonempty G.ColorIndex) (hQ : divisibility A.S) -- Divisors check
open Covering
lemma allLarger {G : Gauge} (A : Levels G) (m : ℕ) : Tendsto (fun i=> (A.S.side m i).val) atTop atTop := tendsto_atTop_mono (f:=fun p=>(A.S.period p).val) (fun i=>Nat.le_mul_of_pos_right _ (A.S.denominator m).property) A.S.period_strict.tendsto_atTop
include h hk hQ hG hX hN hu hv hU hV hp hp' hh
lemma accepted_waves m i t (σ τ : TypeFace 1→G.ColorIndex→ℂ) s (hσ : ∀ i j,‖σ i j‖≤ 1) (hτ : ∀ i j,‖τ i j‖ ≤ 1) :
    let q := loopDrift K (m:=m) (p:=i) hU hV; let p := loopDrift K (m:=m+1) (p:=i) hU hV
    let d := wave t σ + wave s τ; let a := mapBind A M X; q d=p (a m i d) := by
       intro q p d Mmap
       let r p := loopDrift K (m:=m) (p:=p) hU hV; let f p := loopDrift K (m:=m+1) (p:=p) hU hV; let fM t := f t ∘ Mmap m t
       change r i d=fM i d
       have he p (k k') (s r : TypeFace 1→G.ColorIndex→ℂ) (h₁ : ∀ a j, ‖s a j‖≤1) (h₂ : ∀ a j, ‖r a j‖ ≤ 1) := drift_eq K h hk u hu v hv hU hV hX hp hp' hN hh m p k k' s r h₁ h₂ -- z+p duplicates
       obtain ⟨f',hf,H⟩ := show ∃ f':ℕ→ℕ, Tendsto f' atTop atTop ∧ ∀ j:ℕ,(A.S.period i).val ∣ (A.S.period (f' j)).val from by choose f hf hk using fun j=> hQ (A.S.period i) j; exact ⟨f,tendsto_atTop_mono (f:=id) (fun i=>hf i) tendsto_id,hk⟩
       let box n := groups m A.S (H n); let box' n := groups (m+1) A.S (H n)
       let w n := (box n).clone d
       have hb (d' : Dir G (A.S.side m i)) n₀ : (r (f' n₀) ((box n₀).clone d'))= quota (box n₀)*(r i d') := by unfold r loopDrift discrep; rw [(hU m).loopLimit ((A.S.side m (f' n₀))) 2|>.2, (hV m).loopLimit _ 2|>.2, (hU m).loopLimit _ 2|>.2,(hV m).loopLimit _ 2|>.2]; simp only [loop_per_shadow _ (hU _),loop_per_shadow _ (hV _)]; ring
       have hF n : fM (f' n) (w n)=quota (box n)*(fM i d) := by
            change f (f' n) ((mapBind A _ X m (f' n)) ((groups m A.S (H n)).clone d))=quota (groups m A.S (H n))*(f i (mapBind A _ X m i d))
            rw [←across_towers m h hu hX (H n), ←quota_step m h hu hX (H n)]
            unfold f loopDrift discrep
            rw [(hU (m+1)).loopLimit _ 2|>.2,(hU (m+1)).loopLimit _ 2 |>.2,(hV (m+1)).loopLimit _ 2 |>.2,(hV (m+1)).loopLimit _ 2|>.2]
            simp only [loop_per_shadow _ (hU _),loop_per_shadow _ (hV _)]; ring
       have hδ p (l : Dir G (A.S.side m p)) : ruby K hU hV (x m) (y m) m p l =0 := by rw [ruby_equal K h hk u hu v hU hV hX m p _ _ _ hv (fun j => (hh p j).mono (by omega)),alpha_pair K h hk u hu v hv hU hV hX hp hp' hN hh hG m,sub_self,zero_mul]
       let y i : ℝ := (A.S.side m i).val
       let E n := expFee (A.S.side m (f' n)) (Q.c (A.clock.J (m+1)))
       let err := dust (A:=A) Q m
       -- name collision Q post use `post` at variables
       have hprice n : |r (f' n) (w n)-fM (f' n) (w n)| ≤ 8*err (f' n) := by
            rw [show w n=(box n).clone (wave t σ+wave s τ) from rfl,add_clone,tone_lift,tone_lift]; dsimp only [r,fM]; convert he (f' n) _ _ _ _ hσ hτ using 1; rw [hδ,zero_add]; rfl
       let C := 8*(y i)^4 * Q.Γ (A.clock.J (m+1)) * A.clock.loopCap (m+1) -- replace
       have hCut n : |r i d-fM i d| ≤ C*E n := by
            let S := quota (box n)
            have hpos : 0<S := pow_pos (div_pos (by exact_mod_cast (A.S.side _ _).property) (by exact_mod_cast (A.S.side ..).property)) _
            have hp (t) : (y t) ≠ 0 := by unfold y; exact_mod_cast (A.S.side m t |>.property.ne')
            have ht : (quota (box n)) * |r i d-fM i d| ≤ _ := Eq.trans_le (by rw [← abs_of_pos (a:=quota (box n)) hpos,← abs_mul,mul_sub,← hb d n,← hF n]) (hprice n) -- hF reverse
            rw [←le_div_iff₀' hpos] at ht
            refine ht.trans_eq ?_
            unfold err dust tolerance S quota
            rw [site_card,Nat.cast_pow]; change 8*((y (f' n))^4 * _ * _ * E n) / (y (f' n)/y i)^4 = C*E n
            unfold C; field_simp [hp i,hp (f' n)] <;> ring
       have hlim : Tendsto E atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using expfee_tendsto _ ((allLarger A m).comp hf) (Q.c (A.clock.J (m+1))) (Q.posC _) 0
       exact sub_eq_zero.mp <| abs_eq_zero.mp ((le_antisymm (ge_of_tendsto (by simpa only [mul_zero] using hlim.const_mul C) (Eventually.of_forall hCut)) (abs_nonneg _)))
lemma full_recursion m i : let q := loopDrift K (m:=m) (p:=i) hU hV; let p := loopDrift K (m:=m+1) (p:=i) hU hV;
    q=p ∘ mapBind A M X m i := by
  intro q t
  let c j := A.S.side j i
  let E (j) := (hU j).spiralTensor (c j) 2-(hV j).spiralTensor (c j) 2
  let Y := E m
  let J : Matrix (Body 1 (c (m+1))) (Body 1 (c m)) ℝ := installed (A.clock.op m i).ratio (X m)
  let Q : Dir G (c m) →ₗ[ℝ] Dir G (c (m+1)) := {
     toFun := actionFrame J
     map_add' u v := funext fun k=>by change ∑ j,J k j • (u j+v j)=_; simp only [smul_add,Finset.sum_add_distrib]; rfl
     map_smul' a v := funext fun k=>by change ∑ j,J k j • (a • v j)=a • ∑ j,J k j • v j; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _=> by rw [← mul_smul,←mul_smul,mul_comm (J k j) a] }
  let F := Q.toContinuousLinearMap
  let W := (E (m+1)).compContinuousLinearMap (fun (_ : Fin 2)=>F)
  have symm (j : ℕ) {W : ℕ→Shadow G} {u} (hP : ∀ m,woodPassing K u m W) : Tensor.Sym ((hP j).spiralTensor (c j) 2) := by
     let f := spray (fun i' : ℕ=>tread (c j) (K.path (u i') j)) 2
     have ht (x : Fin 2→ Dir G (c j)) := (view_cont (E:=Dir G (c j)) (F:=ℝ)).continuousAt.tendsto.comp (((hP j).loopLimit (c j) 2).1.prodMk_nhds (tendsto_const_nhds (x:=x))) -- view_cont no k implicit check binder
     intro x σ; exact tendsto_nhds_unique (ht (x∘σ)) ((ht x).congr' ((hP j |>.loop_groomed (c j)).mono (fun i hi=> (show f i _ = f i _ from Analysis.sym_Jet (hi.of_le (finite_cap 2)) x σ).symm)))
  have hE x : F x = mapBind A M X m i x := Eq.symm (polish_eval J x)
  have hv' j : Tensor.Sym (E j) := fun t σ=> congr_arg₂ (·-·) (symm j hU t σ) (symm j hV t σ)
  have hW : Tensor.Sym W := fun x v=> (hv' (m+1) (fun j=>F (x j)) v)
  have heq : Y=W := Covering.wave_span (hv' m) hW (fun i' j' σ τ hσ hτ=> ?_)
  · ext z; change Tensor.diagonal Y z = t _; rw [heq]; unfold Tensor.diagonal W; rw [←hE z]; rfl
  change q _ = t (F _)
  rw [hE]; exact accepted_waves K h hk u hu v hv hU hV hX hp hp' hN hh hG hQ m i i' σ τ j' hσ hτ -- hv shadowed.
end YM.UVExt.Paths
