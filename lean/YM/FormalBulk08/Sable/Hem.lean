import YM.FormalBulk08.Sable.Tuft

/-! Propagating Tap without loss of powers at EITHER mesh unit.
Holding roof markers only. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Filter Function Next.Free Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {I V:Type} {u m n:ℕ} {σ η A B :ℝ} {o:edgeL G}
-- diagonal tile cost. Keep anchor for shift.
lemma hearth_inside (a:Loc G 1)(z:hue G)(p:Bool)(k:ℕ)(i:diagD n):∃ B:ℝ,0≤B ∧ ∀ T:Tile (edgeL G) (i.val.1+1),∀ (ε:ℝ≥0),ε ≤ 1 → ∀ (x:Cover)(c:edgeL G), (fame _).d c (x,a) ≤ 1 → ∀ o:edgeL G,
   heft (grain (fame _) ε) (u:ℝ) o c (plaster z (x,a) p k i T)≤ ENNReal.ofReal B * heft (grain (fame _) ε) u o (x,a) (shed T (x,a)):= by
   obtain ⟨K,hK,H⟩:=ash_pledge G a p k i.val.2 z (η:=1)
   let M:ℝ:= i.val.1+1; have hM:0 ≤ M:=by unfold M; positivity
   have hs : 0≤ sack u 1:= sack_pos u one_pos
   refine ⟨Real.exp ((u:ℝ)*plum 1 1)* M*(sack u 1*K),by positivity,fun T ε hb x c hx o=>?_⟩
   let D:=grain (fame (Loc G 1)) ε; let U:=hill z (x,a) p k i.val.2; have hε:(ε:ℝ) ≤ 1:=by exact_mod_cast hb
   have he : D.d c (x,a) ≤ plum 1 1:= by
      refine (plum_mono hx).trans (Nat.ceil_mono ?_); apply Real.log_le_log (by positivity); simpa using hε
   have ht : (∑' v, penon D (x,a) u U v) ≤ ENNReal.ofReal (sack u 1*K):= (sack_to u (by norm_num) hb (H x)).2
   apply le_trans (loom_away _ he (Nat.cast_nonneg _) _) _; rw [plaster,vapor_scale,polish_grade,ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le hM)]; have hv := (polish_s (D:=D) (x:=o) (a:=(x,a)) (η:=u) _).trans (vapor_clasp (Nat.cast_nonneg _) (shed T (x,a)) U); refine (mul_le_mul_right (mul_le_mul_right (hv.trans (mul_le_mul_right ht _)) _) _).trans_eq ?_; rw [show (↑(i.val.1+1) :ℝ)=M from Nat.cast_add_one _,←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg hM,ENNReal.ofReal_mul (Real.exp_pos _).le]; unfold Gorge.shine; ring
lemma shores (w v: Loc G 1) (z:hue G)(l: ℕ ×ℕ)(n:ℕ)(b:Bool):∃ B:ℝ,0≤B ∧ ∀ T:Pot G,∀ (ε:ℝ≥0),ε ≤ 1 →∀ A:ℝ, (∀ i:ℕ,Nat.succ 0 ≤ i → i≤ n+1 → Knoxville (grain (fame _) ε) u o (T l.1 i) A) →∀ f:Cover→Cover, Injective f→ (∀ x,(fame _).d (x,w) (f x,v) ≤1) →
      (∑' x:Cover, heft (grain (fame _) ε) u o (x,w) (shapeD z (f x,v) b l n T)) ≤ ENNReal.ofReal B* ENNReal.ofReal A:= by
    let S:=Finset.antidiagonal n; choose K hK H using fun i:diagD n=> hearth_inside (u:=u) v z b l.2 i
    refine ⟨∑ i∈S.attach,K i, Finset.sum_nonneg (fun i _=>hK _),fun T ε hb A hp f Hf hv=>?_⟩
    let D:=grain (fame (Loc G 1)) ε; unfold shapeD; rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>hK i), Finset.sum_mul]; apply (ENNReal.tsum_le_tsum (g:=fun x:Cover=>∑ i∈S.attach, heft D (u:ℝ) o (x,w) (plaster z (f x,v) b l.2 i (T l.1 (i.val.1+1)))) (fun i=> vapor_sum (x:=o) (a:=(i,w)) _ _)).trans; rw [Summable.tsum_finsetSum (fun i _=>ENNReal.summable)]; refine Finset.sum_le_sum fun i _=>?_
    let U:= T l.1 (i.val.1+1); have he:= Finset.mem_antidiagonal.mp i.property; have h: (∑' x:edgeL G, heft D (u:ℝ) o x (shed U x)) ≤ ENNReal.ofReal A:= by
       rw [←heft_p]; exact (hp _ (by omega) (by omega)).2
    refine (ENNReal.tsum_le_tsum (fun x:Cover=> H i U ε hb _ (x,w) (hv x) o)).trans ?_; rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right ((ENNReal.tsum_comp_le_tsum_of_injective (show Injective (fun x:Cover=>(f x,v)) from fun x y he=>Hf (congr_arg Prod.fst he)) _).trans h) _
lemma sailor (w:Loc G 1)(z:hue G)(l:ℕ×ℕ)(n:ℕ):∃ B:ℝ,0≤B∧∀ T:Pot G,∀ (ε:ℝ≥0),ε ≤ 1 →∀ A:ℝ,(∀ i:ℕ,Nat.succ 0 ≤ i →i≤n+1 → Knoxville (grain (fame _) ε) u o (T l.1 i) A) →
     (∑' x:Cover, heft (grain (fame _) ε) u o (x,w) (cruisesD z x l n T)) ≤ ENNReal.ofReal B* ENNReal.ofReal A:= by
   choose B hB H using fun (v:Loc G 1)(b:Bool)=> shores (o:=o) (u:=u) w v z l n b
   refine ⟨∑ v,(B v true+B v false), Finset.sum_nonneg (fun i _=>add_nonneg (hB ..) (hB ..)),fun T ε hb A hp=>?_⟩
   let D:= grain (fame (Loc G 1)) ε;
   let F(x:Cover)(v:Loc G 1):=shapeD z (x,v) true l n T; let P(x:Cover)(v:Loc G 1) := shapeD z (backwards x v.1,v) false l n T
   rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>add_nonneg (hB ..) (hB ..)),Finset.sum_mul]; unfold cruisesD; apply (ENNReal.tsum_le_tsum (g:=fun x=> ∑ v,heft D (u:ℝ) o (x,w) (F x v+P x v)) (fun x=>vapor_sum ..)).trans;rw [Summable.tsum_finsetSum (fun _ _=> ENNReal.summable)]; apply Finset.sum_le_sum;intro i _
   refine (ENNReal.tsum_le_tsum (fun x:Cover=> vapor_plus (D:=D) (η:=u) (F x i) (P x i) o (x,w))).trans ?_; rw [ENNReal.tsum_add,ENNReal.ofReal_add (hB ..) (hB ..), add_mul]; apply add_le_add
   · exact H i true T _ hb A hp id Function.injective_id (fun _=>by simp [fame,capD,size])
   apply H i false T _ hb A hp (fun x=>backwards x i.1) (fun a b he=> sub_left_injective he)
   intro x; simp [fame,capD,size,backwards,apply_ite Int.natAbs]

lemma soak (e r:ℕ)(u:ℕ)(o:edgeL G):∃ C:ℝ,0≤C ∧∀ T:Pot G,Authorized T → Agate (T e (r+1)) → ∀ (ε:ℝ≥0),ε≤1 → ∀ B,0≤B →(∀ j<e,∀ w, 1≤w → w≤ r+1 → Knoxville (grain (fame _) ε) u o (T j w) B) → Knoxville (grain (fame _) ε) u o (tap (T e (r+1))) (C* B):= by
    let Z: Finset (ℕ×ℕ):= (Finset.antidiagonal e).erase (e,0)
    choose S hS H using fun (w:Loc G 1)(t:ℕ ×ℕ)=> sailor (u:=u) (o:=o) w w.2 t r
    let L:ℝ:=(r+1:ℕ); have hl:0<L:=by unfold L; positivity
    let Q(w:Loc G 1):= |-L⁻¹| *∑ i∈Z,S w i
    have hQ w:0≤Q w:=mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _=> hS w i))
    let C:=∑ w,Q w; have hc:0≤C:= Finset.sum_nonneg (fun w _=>hQ w)
    refine ⟨C,hc,fun V hV hx ε hp B hB hv=>⟨mul_nonneg hc hB,?_⟩⟩
    let F:=tap (V e (r+1)); let U(w:Loc G 1)(x:Cover):=∑ t∈Z,cruisesD w.2 x t r V; let D:=grain (fame (Loc G 1)) ε
    have hg x (w:Loc G 1) : shed F (x,w)= -L⁻¹ • U w x:= by
        have he:=hV w.2 x e r; rw [←Finset.add_sum_erase _ _ (a:= (e,0)) (by simp), cruise_head w.2 V _ hx] at he
        have hh:L • shed F (x,w)= -U w x:= by rw [show shed F _= riverP w.2 x (V e (r+1)) from funext fun v=>by simp only [Lava.shed,F,tap,Fin.cons_zero,Fin.tail_cons]]; exact eq_neg_of_add_eq_zero_left he
        rw [neg_smul,←smul_neg,←hh,←mul_smul,inv_mul_cancel₀ hl.ne',one_smul]
    change (∑' v, penon D o u F v)≤ _; rw [heft_p, ENNReal.ofReal_mul hc]; unfold C; rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>hQ i), Finset.sum_mul]; rw [ENNReal.tsum_prod', ENNReal.tsum_comm (f:=fun x w=> heft D (u:ℝ) o (x,w) (shed F (x,w))),tsum_fintype]; refine Finset.sum_le_sum fun w _=>?_ ; simp_rw [hg,vapor_scale]; rw [ENNReal.tsum_mul_left]; unfold Q; rw [ENNReal.ofReal_mul (abs_nonneg _)]; rw [←Real.norm_eq_abs,ofReal_norm] -- abs on P but ofReal_mul needed
    apply le_trans _ (le_refl _)
    apply le_trans (mul_le_mul_right (ENNReal.tsum_le_tsum (fun x:Cover=>vapor_sum (D:=D) (η:=u) (x:=o) (a:=(x,w)) Z _)) _)
    rw [Summable.tsum_finsetSum (fun _ _=> ENNReal.summable),ENNReal.ofReal_sum_of_nonneg (fun i _=> hS w i), mul_assoc, Finset.sum_mul]
    apply mul_le_mul_right; refine Finset.sum_le_sum fun i hi=> H w i V ε hp B (hv i.1 (by have he:=Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hi); have ht:=Finset.ne_of_mem_erase hi; by_contra hg; apply ht; exact Prod.ext (by dsimp;omega) (by dsimp;omega)))
end YM.FormalBulk08.Sable
