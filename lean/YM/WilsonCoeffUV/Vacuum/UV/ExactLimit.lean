import YM.WilsonCoeffUV.Vacuum.UV.StepLimit
/-!
# Limit adjacent reclosure and Ward

Order domains need not allow calling non-admitted orders (even at same
reporting site) with uniform constants. `Doric` is the finite projection of the
coeff conditions. Does not set all higher orders to zero (vertical identity).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W :Credit}{α β ξ:Type*}{s a:ℝ}{θ:ℕ→ℝ}
section
variable {X:Type*}[NormedAddCommGroup X]{x:ℕ→X}{y:X}
lemma gleam (p:Tendsto θ atTop (𝓝 0))(h:∀ᶠ n in atTop,twain a (θ n) (x n) y): Tendsto x atTop (𝓝 y):=by
   rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (h.mono (fun u e=> e.gap)) ?_
   simpa only [mul_zero] using p.const_mul a
lemma beacon {P:ℕ→ Ten ℝ (YForest G) 2}{K:Ten ℝ (YForest G) 2}(h:Cape θ s P K)(hp:Tendsto θ atTop (𝓝 0))(he:0<s): Tendsto (fun i=>readSun (P i)) atTop (𝓝 (readSun K)):=by obtain ⟨a,h⟩:=h; exact gleam hp (h.mono fun n v=> note_kin v he)
end
section
variable {P:ℕ→ Cost}{Q:Cost} {p:ℕ→Cost}{q:Cost}
def Rising (P:ℕ→ Cost)(Q: Cost)(k:ℕ): Prop:= Tendsto (fun i=>coeff k (P i)) atTop (𝓝 (coeff k Q))
lemma Rising.mul (h:∀ j≤ i,Rising P Q j)(e:∀ j≤ i,Rising p q j): Rising (P * p) (Q*q) i:=by unfold Rising; simp_rw [Pi.mul_apply,coeff_mul]; apply tendsto_finsetSum; intro x hx; have he:= Finset.mem_antidiagonal.mp hx; exact Tendsto.mul (h x.1 (by omega)) (e x.2 (by omega))
lemma Rising.pow (h:∀ j≤ i,Rising P Q j) (n):Rising (P^n) (Q^n) i:=by
   induction n generalizing i with
   | zero=> simp only [pow_zero]; exact tendsto_const_nhds
   | succ k ih=> rw [pow_succ,pow_succ]; exact Rising.mul (fun j hj=> ih fun a ha=> h a (ha.trans hj)) h
lemma Rising.inv (h:∀ j≤ i,Rising P Q j)(p: ∀ᶠ n in atTop, constantCoeff (P n)=1)(e:constantCoeff Q=1): Rising (fun i=>(P i)⁻¹) (Q⁻¹) i:=by
   induction i using Nat.strong_induction_on with
   | h i ih=>
      by_cases hb:i=0
      · subst i; unfold Rising; simp_rw [coeff_zero_eq_constantCoeff_apply]; exact tendsto_const_nhds.congr' (p.mono fun n hv=> by simp [hv,e])
      let S:= (Finset.antidiagonal i).erase (0,i)
      have hh j (hj:j∈S): j.2 < i ∧ j.1≤ i:= by obtain ⟨x,hx⟩:= Finset.mem_erase.mp hj; have he:= Finset.mem_antidiagonal.mp hx; refine ⟨?_,by omega⟩; by_contra! he; exact x (Prod.ext (show j.1=0 by omega) (show j.2=i by omega))
      have hg := (tendsto_finsetSum S (fun j hj=> Tendsto.mul (h j.1 (hh j hj).2) (ih j.2 (hh j hj).1 fun a ha=> h a (ha.trans (hh j hj).1.le)))).neg
      unfold Rising; rw [stem_amt Q e i (by omega)]; exact hg.congr' (p.mono fun i' hi=> (stem_amt _ hi _ (by omega)).symm)
lemma Rising.back (h:∀ j≤ i, Rising P Q j)(p:∀ᶠ n in atTop, constantCoeff (P n)=1)(e:constantCoeff Q=1): Rising (fun i=> Blue.back (P i)) (Blue.back Q) i:=by
   induction i using Nat.strong_induction_on with
   | h i ih=>
     by_cases hb:i=0
     · subst i; unfold Rising; simp_rw [coeff_zero_eq_constantCoeff_apply, back_cc e]; exact tendsto_const_nhds.congr' (p.mono fun j hj=> (back_cc hj).symm)
     let S:= (Finset.range (i+1)).erase 0; let T:= ((Finset.antidiagonal i).erase (0,i)).erase (i,0)
     have hd j (e:j∈S): j≤ i ∧ i-j < i:= by obtain ⟨x,w⟩:= Finset.mem_erase.mp e; have he:= Finset.mem_range.mp w; omega
     have hf j (e:j∈T): j.1 < i ∧ j.2 < i:= by
        obtain ⟨x,w⟩:=Finset.mem_erase.mp e; obtain ⟨p,hp⟩:=Finset.mem_erase.mp w; have he:= Finset.mem_antidiagonal.mp hp; constructor; · by_contra! h; exact x (Prod.ext (show j.1=i by omega) (show j.2=0 by omega))
        by_contra! h; exact p (Prod.ext (show j.1=0 by omega) (show j.2=i by omega))
     have hh k (hk:k < i):= ih k hk (fun j hj=>h j (hj.trans hk.le))
     have H:= (Tendsto.sub (tendsto_finsetSum S (fun a ha=> Tendsto.mul (h a (hd a ha).1) (Rising.pow (i:=i-a) (fun k hk=>hh k (lt_of_le_of_lt hk (hd a ha).2)) a))) (tendsto_finsetSum T (fun j hj=> Tendsto.mul (hh _ (hf j hj).1) (hh _ (hf j hj).2)))).const_mul ((1/2):ℝ)
     unfold Rising; rw [signal_square Q e i (by omega)]; exact H.congr' (p.mono fun n hv=> (signal_square (P n) hv _ (by omega)).symm)
end

variable (R:Realm G e U)
lemma evergreen (h:R.anchor≤m)(p:k≤ e): Rising (fun n=> pitch R.draws R.paid n m) (viridian R.draws R.paid m) k:= by unfold Rising pitch viridian; simp only [stellar_read]; exact beacon (eternal_phase _ h p 2) (R.ωJ_vanish _) (R.mint m h).width
lemma one_sun (h:R.anchor≤m): constantCoeff (viridian R.draws R.paid m)=1:=by
    have he:= evergreen R h (Nat.zero_le e); unfold Rising at he; simp_rw [coeff_zero_eq_constantCoeff_apply] at he; exact tendsto_nhds_unique he (tendsto_const_nhds.congr' ((eventually_gt_atTop m).mono (fun n hn=>(angle_tilt R.hG R.green hn).symm)))
lemma brushSun (h:R.anchor≤m)(p:k≤ e)(a b): Rising (fun n=> ratioHigh R.draws R.paid n m^a*((ratioHigh R.draws R.paid n m)⁻¹)^b) ((back (viridian R.draws R.paid m))^a*((back (viridian R.draws R.paid m))⁻¹)^b) k:= by
    let f i:=ratioHigh R.draws R.paid i m; let g:=back (viridian R.draws R.paid m)
    have he:∀ᶠ n in atTop,constantCoeff (pitch R.draws R.paid n m)=1 := (eventually_gt_atTop m).mono fun n hn=>angle_tilt R.hG R.green hn
    have hh j (p:j≤ e): Rising f g j:= Rising.back (fun i hi=> evergreen R h (hi.trans p)) he (one_sun R h)
    exact Rising.mul (P:=fun i=> f i ^a) (fun i q=> Rising.pow (P:=f) (fun j w=>hh j (w.trans (q.trans p))) _) (p:=fun i=>(f i)⁻¹^b) (fun j w=> Rising.pow (P:=fun i=>(f i)⁻¹) (fun x u=> Rising.inv (fun i hi=> hh i (by omega)) (he.mono fun i hi=>back_cc hi) (back_cc (one_sun R h))) _)
lemma key_turn (h:R.anchor≤m)(p:k≤ e)(hf:k%2≠0) : coeff k (viridian R.draws R.paid m)=0:= by
    apply tendsto_nhds_unique (show Tendsto (fun i=>coeff k (pitch R.draws R.paid i m)) _ _ from evergreen R h p) (tendsto_const_nhds.congr' ((eventually_gt_atTop m).mono (fun i hi=>?_)))
    exact ((perch R.draws R.paid R.hG R.green hi).parityC k hf).symm
lemma sustainable (h:R.anchor≤m)(p:k≤ e): timeless R.draws R.paid m k= Blue.mix (back (viridian R.draws R.paid m)) (lop (eternal R.draws R.paid m)) k:=by
   funext r x
   have ht:= timeless_pt p R h r x
   refine tendsto_nhds_unique ht (f:=fun n=> actionW R.draws R.paid n m k r x) ?_
   refine Tendsto.congr' (f₁:=fun n=> Blue.mix (ratioHigh R.draws R.paid n m) (lop (freshet R.draws R.paid n m)) k r x) ((eventually_gt_atTop m).mono fun n hn=> by dsimp only; rw [conduct R.draws R.paid hn]) ?_
   simp_rw [Blue.mix, Finset.sum_apply,Pi.smul_apply]; apply tendsto_finsetSum; intro j hj; have he:= Finset.mem_range.mp hj; refine Tendsto.smul (brushSun R h (show k-j≤e by omega) j r) ?_
   unfold lop; split; · exact tendsto_const_nhds
   exact (eternal_phase R h (show j≤ e by omega) _).lit (R.ωJ_vanish m) x

-- Wick lamp limit. every finite order through at MOST k.

def pillar {V:Type*}[AddCommGroup V][Module ℝ V] (P:Pal V (YForest G))(k:ℕ): Prop:= ∀ (b:G.Color)(x:Cover), ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (wickLamp b 0 (x,v) j z.1 (P z.2) + wickLamp 0 b (x-step v,v) j z.1 (P z.2))=0
lemma lamp_sure {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{P:ℕ→ Gen V (YForest G)}{F: Gen V (YForest G)}(h:∀ i x,Tendsto (fun n=>P n i x) atTop (𝓝 (F i x))) (a b:G.Color)(u:Edge Cover)(j:G.ColorIndex)(k r:ℕ)(x): Tendsto (fun n=> wickLamp a b u j k (P n) r x) atTop (𝓝 (wickLamp a b u j k F r x)):=by
   by_cases H:k≤r; swap; · simp_rw [wick_pos _ _ _ _ _ (Nat.lt_of_not_ge H)]; exact tendsto_const_nhds
   simp_rw [wick_leg _ _ _ _ _ H,swirl, Pi.smul_apply,Finset.sum_apply]; refine Tendsto.const_smul (tendsto_finsetSum _ (fun i _=>?_)) _
   simp only [interweave,dif_pos (show k+(r-k)=r by omega),sever, Pi.smul_apply,prune]; exact ((h _ _).const_smul _).const_smul _
lemma perseveres (h:R.anchor≤m)(p:k≤ e): pillar (timeless R.draws R.paid m) k:=by
   let F n:= actionW R.draws R.paid n m
   let W:= timeless R.draws R.paid m
   intro b x
   let V n:= ∑ v: Axis,∑ j:G.ColorIndex,∑ z∈ Finset.antidiagonal k, (wickLamp b 0 (x,v) j z.1 (F n z.2)+wickLamp 0 b (x-step v,v) j z.1 (F n z.2))
   have ha : ∀ᶠ n in atTop, V n=0:= (eventually_ge_atTop m).mono fun n hn=> (catchment R.draws R.paid R.hG R.green hn).separate b x k
   funext l w
   refine tendsto_nhds_unique (l:=(atTop:Filter ℕ)) (f:=fun n=>V n l w) ?_ (tendsto_const_nhds.congr' (ha.mono fun n hn=>by dsimp only; rw [hn]))
   simp_rw [V,Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro j _; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro v hv
   have he : v.2 ≤ e:= by have hh:= Finset.mem_antidiagonal.mp hv; omega
   exact (lamp_sure (P:=fun n=>F n v.2) (fun r=> timeless_pt he R h r) _ _ _ _ _ _ w).add (lamp_sure (P:=fun n=>F n v.2) (fun r=> timeless_pt he R h r) _ _ _ _ _ _ w)
end YM.WilsonCoeffUV.Bank
