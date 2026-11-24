import YM.OPE.Compatible.Glow.Greet
import YM.OPE.Compatible.Grid.Lead
/-! # Epic stencils on cover log inputs -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}
namespace Script
open Page
lemma pointBill (G:Gauge) (d:ℕ)(c:ℝ)(hp:0 ≤ c):∃ U:ℝ,0 ≤ U∧∀ (w:Walk)(p:Cover)(x:fieldX (Shade G)),(∀ i∈ dirt p w,‖indexS i x‖ ≤ c)→ ∀ t, ‖iteratedDeriv d (fun t:ℝ=>G.mat (travel (lotU (t • x)) p w)) t‖ ≤ U*(w.length+1:ℝ)^d:=by
     obtain ⟨U,hU,H⟩:= stewRace G _ hp _; refine ⟨U,hU,fun w p x h t=>?_⟩; have hl: (pieces x p w).length=w.length:=by
        clear h; induction w generalizing p with | nil=>rfl| cons i w ih=>simp [pieces,ih]
     simp_rw [syntaxU]; rw [← (show (pieces x p w).length= _ from hl)]; exact H _ _ (ticket_pieces _ _ _ _ h) --
lemma tapOx (G:Gauge)(U:ℝ)(hp:0≤U)(j:ℕ):∃ C:ℝ,0 ≤ C∧ ∀ (p:Beam G)(x:fieldX (Shade G)) (d:ℝ),0≤ d→(∀ x:G.Mat, ‖p.f x‖ ≤ d*‖x‖)→ (∀ i∈dirt 0 p.leg, ‖indexS i x‖≤ U)→∀ t:ℝ,‖iteratedDeriv j (fun v=> p.shot v x) t‖ ≤ C*d*(p.leg.length+1:ℝ)^j:=by
    obtain ⟨g,hg,H⟩:=pointBill G j U hp; let v:G.Mat:=1; refine ⟨g+‖v‖,add_nonneg hg (norm_nonneg _),fun p x D hD hv h t=>?_⟩; let f(t:ℝ):= G.mat (travel (lotU (t • x)) 0 p.leg); let S:=(p.leg.length+1:ℝ)^j; have hx:1 ≤ S:=by apply one_le_pow₀; simp
    have ht(t): ‖iteratedDeriv j f t‖ ≤ g*S:=H _ _ _ h t; have he:ContDiff ℝ ⊤ f:=fluted ..; let Y:ℝ→G.Mat:=fun _=>1
    change ‖iteratedDeriv j (p.f ∘ (f-Y)) t‖≤_
    have hr:iteratedDeriv j (p.f ∘ (f-Y)) t= p.f (iteratedDeriv j (f-Y) t):=by unfold iteratedDeriv; erw [p.f.iteratedFDeriv_comp_left ((show ContDiff ℝ ⊤ (f-Y) from he.sub contDiff_const).contDiffAt) le_top];rfl
    rw [hr]; apply (hv _).trans; rw [iteratedDeriv_sub _ _]; swap; · exact he.contDiffAt.of_le le_top
    swap; · exact contDiffAt_const
    have hv9: ‖iteratedDeriv j Y t‖ ≤ ‖v‖:=by
        by_cases hh:j=0; · subst j; rw [iteratedDeriv_zero]
        have he : iteratedDeriv j Y t=0:=by unfold Y iteratedDeriv; rw [iteratedFDeriv_const_of_ne hh];rfl
        rw [he,norm_zero]; positivity
    have hz:= (norm_sub_le (iteratedDeriv j f t) (iteratedDeriv j Y t)).trans (add_le_add (ht t) (hv9.trans (le_mul_of_one_le_right (norm_nonneg _) hx)))
    exact (mul_le_mul_of_nonneg_left hz hD).trans_eq (by unfold S; ring)
lemma ozone (G:Gauge)(n:ℕ)(c D:ℝ)(hc:0≤c)(hd:0≤D)(k:ℕ):∃ A:ℝ, 0≤A ∧ ∀ (p:Chant G n)(U:fieldX (Shade G)), moderateX p D → (∀ i∈ cashX p, ‖indexS i U‖ ≤ c) → ∀ t, ‖iteratedDeriv k (fun t:ℝ=>verseX p (lotU (t • U))) t‖ ≤ A*(lawn p+1:ℝ)^k:=by
    induction n generalizing k with
    | zero=>
       refine ⟨1,zero_le_one,fun p U h H t=>?_⟩; simp only [lawn,verseX,Fin.prod_univ_zero,Fin.sum_univ_zero,Nat.cast_zero,zero_add,one_pow,mul_one]; by_cases hk:k=0
       · subst k; simp
       unfold iteratedDeriv; rw [iteratedFDeriv_const_of_ne hk]; simp
    | succ n ih=>
       choose A ha HA using fun i=>ih i; choose F hf H using fun i=> tapOx G _ hc i
       let Y(j:ℕ):ℝ:= (k.choose j:ℝ)*(F j*D)*A (k-j); have hy(j):0 ≤ Y j:=by unfold Y; have hv:= hf j; have ht:=ha (k-j); positivity
       refine ⟨∑ i∈range (k+1),Y i, sum_nonneg fun i _=>hy i,fun p u h hh t=>?_⟩
       let R:=p 0; let v(i:Fin n):=p i.succ; let f(x:ℝ):=R.account (lotU (x • u)); let w(x:ℝ):=verseX v (lotU (x • u)); let T:ℝ:=lawn p+1; have hR: lawn p=R.leg.length+lawn v:=Fin.sum_univ_succ _; have ht:T≥1:=by unfold T; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
       have hi(i): ‖iteratedDeriv i f t‖≤F i * D*T^i:= (H i R u _ hd (h _) (fun j hj=> hh j (mem_biUnion.mpr ⟨0,mem_univ _,hj⟩)) t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show R.leg.length+ (1:ℝ)≤T from by unfold T; rw [hR,Nat.cast_add]; linarith only [Nat.cast_nonneg (α:=ℝ) (lawn v)]) _) (mul_nonneg (hf _) hd))
       have hb(i): ‖iteratedDeriv i w t‖≤ A i*T^i:=(HA _ _ u (fun j=> h j.succ) (fun j h'=>hh j (by obtain ⟨a,-,hA⟩:=mem_biUnion.mp h'; exact mem_biUnion.mpr ⟨a.succ,mem_univ _,hA⟩)) t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show (lawn v:ℝ)+1≤T from by unfold T; rw [hR,Nat.cast_add]; linarith only [Nat.cast_nonneg (α:=ℝ) R.leg.length]) _) (ha _))
       have hT: ContDiff ℝ ⊤ f:=by
          let y: Fin 1→Beam G:= fun _=>R; have he := cash_smooth y u; rwa [show (fun t:ℝ=>verseX y (lotU (t • u)))=f from funext fun i=>by unfold verseX; rw [Fin.prod_univ_one]] at he
       have he : (fun t:ℝ=>verseX p (lotU (t • u)))=f*w:=funext fun i=>Fin.prod_univ_succ _
       rw [he,iteratedDeriv_mul (hT.of_le le_top|>.contDiffAt) ((cash_smooth v u).of_le le_top|>.contDiffAt)]; apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i hij; rw [norm_mul,norm_mul, Real.norm_natCast]; apply (mul_le_mul (mul_le_mul_of_nonneg_left (hi _) (Nat.cast_nonneg _)) (hb _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hi i)))).trans_eq; unfold Y; have hl: i≤k:= Nat.le_of_lt_succ (Finset.mem_range.mp hij); have hv:T^i*T^(k-i)=T^k:=by rw [← pow_add,Nat.add_sub_of_le hl]
       change _=Y i*T^k; unfold Y; rw [← hv]; ring
end Script
end YM.OPE.Flume
