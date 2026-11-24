import YM.OPE.Short.Tail

/-!
# Bounded ratio stress test of finite-factorization logarithmic control

Applies a fixed common Reader, same finite trees, topology/geometry as power
result of `Nesting.Endpoint`. Epsilon-free when contracting through scalar
sectors via `flow` along the weak matching trajectory. No positive-order
matching or assertion of a size continuum in this sharpened estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Sparse.Tracing Nesting.Motion Extraction Pert
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives
variable {n:ℕ}{f:Fin n→Nesting.Tree} (h:Services C F S){M η b:ℝ}
local notation "tree"=> fork n f
open Sparse.Tracing Currency
local notation "shape"=> Measuring.Tree.Nonroot f
def Flux(s:(fork n f|>.Inner)→ℝ)(b:ℝ):= 0 < b ∧ b ≤ 1 ∧ ∀ p:Measuring.Tree.Nonroot f,b≤ (fork n f).ratios 1 s (.inr p)

lemma compatible (t:Tree) {b:ℝ}(h:0 < b): ∃ δ:ℝ,0 < δ ∧ δ ≤ b ∧ ∀ r:ℝ,0<r→ ∀ s:(t.Inner→ℝ), (∀ p:t.Inner,b ≤ t.ratios r s p) → ∀l,r*δ ≤ s l:=by
    have he {a:ℝ}(ha:0<a): ∀ᶠ j:ℝ in 𝓝[>]0, j≤ a:=(ge_mem_nhds ha).filter_mono nhdsWithin_le_nhds
    induction t with
    | bud=> exact ⟨b,h,le_rfl,fun _ _ _ _ e=> by cases e⟩
    | fork n f ih=>
       choose d hd hd' haux using ih
       have hp₀ : ∀ᶠ j:ℝ in 𝓝[>]0,0 < j := self_mem_nhdsWithin
       obtain ⟨δ,⟨hb,hh⟩,hδ⟩:=((hp₀.and (he h)).and (eventually_all.mpr fun j:Fin n=>he (a:=b*d j) (mul_pos h (hd j)))).exists -- grouping fix
       refine ⟨δ,hb,hh,fun r hr s hT l=>?_⟩
       rcases l with z|⟨j,l⟩
       · cases z; exact (mul_comm ..).trans_le ((mul_le_mul_of_nonneg_right hh hr.le).trans ((le_div_iff₀ hr).mp (hT (Sum.inl ()))))
       let a:=s (Sum.inl ()); have ht:r*b ≤ a:= (mul_comm ..).le.trans ((le_div_iff₀ hr).mp (hT (Sum.inl ())))
       have ha:= haux j a ((mul_pos hr h).trans_le ht) (childAge j s) (fun p=>hT (Sum.inr ⟨j,p⟩)) l
       exact (mul_le_mul_of_nonneg_left (hδ j) hr.le).trans ((by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ht (hd j).le : r*(b*d j) ≤ a*d j)|>.trans ha)

private lemma portal {t:Nesting.Tree}{r δ M η:ℝ}(hη:0≤η)(hM:0≤M){s:t.Inner→ℝ}{z:t.Plot} (h:Tapered t r 1 s)(hh : Relative M η t s z)(hδ:∀p,r*δ ≤ s p): Stayed M (η*δ) r t z:=by induction t with
   | bud=>exact True.intro
   | fork n f ih=>
       have he(i:Fin n):=ih i ((h.2.2 i).mono le_rfl (by rw [mul_one]; exact h.2.1)) (hh.2.2 i) (fun l=> hδ (Sum.inr ⟨i,l⟩))
       have hc : η*δ*r ≤ η*s (Sum.inl ()) :=by rw [mul_assoc,mul_comm δ r]; exact mul_le_mul_of_nonneg_left (hδ _) hη
       refine ⟨⟨?_ , fun i j hij=> hc.trans (hh.2.1 i j _ _ hij)⟩, ⟨?_, ?_⟩, he⟩
       · intro i; exact (hh.1 _).trans (mul_le_mul_of_nonneg_left (h.within le_rfl _) hM) -- with z
       · exact fun p=> (hh.1 _).trans (mul_le_mul_of_nonneg_left (h.within le_rfl _) hM)
       rintro ⟨i,u⟩ ⟨i',u'⟩ hij; rcases eq_or_ne i i' with hi|hh'
       · subst i'; have htu : f i≠bud:= by by_contra h'; haveI:=Nonempty.some (Composite.bud_leaf h'); exact hij (congrArg (Sigma.mk i) (Subsingleton.elim ..))
         exact (he i |>.within htu |>.spaced u u') (fun hU =>hij (congrArg (Sigma.mk i) hU))
       exact hc.trans (hh.2.1 i i' _ _ hh')

variable (hM:0≤M)(hη:0<η)
include hM hη
private lemma demand (hb:0 < b) (f:Fin n→Nesting.Tree) : ∃ α:ℝ,0<α ∧ ∀ r:ℝ, ∀s,∀z, Accept r M η (t:=fork n f) s z → Flux s b → Stayed M α r (fork n f) z:=by
     obtain ⟨δ,hδ,-,hg⟩:=compatible (fork n f) hb
     refine ⟨η*δ,mul_pos hη hδ,fun r s z hc hb=>portal hη.le hM hc.levels hc.relative (hg _ (hc.levels.positive (.inl ()) |>.trans_eq hc.scale) _ ?_)⟩
     intro u; rcases u with ⟨⟩|p
     · exact ((div_self ((hc.levels.positive (.inl ())).trans_eq hc.scale).ne').symm ▸ hb.2.1).trans_eq ((congr_arg (· / r) hc.scale).symm)
     exact hb.2.2 p
omit hM hη
section
include hG h hM hη H
attribute [local instance] Classical.decEq
private lemma fees (c:R.channels 0)(D:(fork n f|>.Inner)→ℕ)(ab:Picture (Leaf tree)){b:ℝ}(hb:0<b)(hD:∀ i:Measuring.Tree.Nonroot f,D (.inr i) ≤ 3): ∃ A:ℝ,0 ≤ A ∧ ∀ᶠ k in atTop,∀s:(fork n f).Inner→ℝ, ∀ z:(fork n f).Plot,Accept (X.r k) M η s z→ Flux s b →
    let Y:= (X.r k)^(-(levy (fork n f):ℝ))
    let p:= stressTag U ab
    ‖Kernel.output U R z p c‖ ≤ A*Y ∧ ‖Kernel.chord U R z p c D‖ ≤ A*Y:=by
      obtain ⟨α,hα,he'⟩:= demand hM hη hb f
      let D':=Currency.reset D
      have ht:Composite.boundNow (fork n f) D'=0:=rfl
      obtain ⟨A,hA,he⟩:=nested_term U R X hG H h hM hα c D' ab (born D hD)
      obtain ⟨B,hB,hB'⟩:=payment U R X hG H ab hM hα h c
      let p:=(stressTag U ab)
      let c' := (uniform U R h).direct n f p 0 c D' M η 1 hM hη zero_lt_one
      have hk:Tendsto X.r atTop (𝓝[>]0):=tendsto_nhdsWithin_iff.mpr ⟨X.drips,Eventually.of_forall X.positive⟩
      refine ⟨A+B,add_nonneg hA hB,?_⟩
      filter_upwards [he,hB',hk.eventually c'] with k hk hf hr s z hz hs
      let Y:ℝ:= (X.r k)^(-(levy (fork n f):ℝ))
      have hP:0≤ Y:=Real.rpow_nonneg (X.positive k).le _
      have h':= he' _ _ _ hz hs
      refine ⟨(hf (profile z) (anchor z) h'.2.1).trans (show _ ≤ (A+B)*Y from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hP),?_⟩
      let F':= Kernel.aperture U R (fork n f)
      calc _ = ‖Kernel.chord U R z _ c D'‖ := congr_arg norm (by
                    rw [nested_zero U R,nested_zero U R]
                    apply congr_arg (fun q => R.coef 0 c (skyline z) (voices q) (anchor z)); funext j; unfold Sparse.Circuit.Children.each
                    exact congr_arg (fun p=>Sparse.Circuit.Children.issue U R (childPlace j z) (childWages j (stressTag U ab)) p) (show childAge j D=childAge j D' from funext fun j=> rfl))
           _ ≤ _ :=(hk z (by erw [ht]; exact (hr s z hz).2.1) h').trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hP)

private lemma outright_mid (c:R.channels 0)(D:(fork n f|>.Inner)→ℕ)(ab:Picture (Leaf tree)){b:ℝ}(hb:0<b)(hD:∀ i:Measuring.Tree.Nonroot f,D (.inr i) ≤ 3):∃ A:ℝ,0 < A ∧ ∀ᶠ k in atTop,∀s:(fork n f).Inner→ℝ, ∀ z:(fork n f).Plot,Accept (X.r k) M η s z→ Flux s b →
    (let p:=stressTag U ab; let B:=toll (wages p) 0 0 s; ‖Kernel.output U R z p c‖ ≤ A * B) ∧ ‖Kernel.output U R z (stressTag U ab) c -Kernel.chord U R z (stressTag U ab) c D‖ ≤ A * bothToll (wages (stressTag U ab)) 0 0 D s:=by
       obtain ⟨A',hA,hx⟩:=fees U R X hG H h hM hη c D ab hb hD
       let p:=stressTag U ab
       let B (s):=toll (wages p) 0 0 s
       have ht : ∀ᶠ k in atTop,∀ s,∀ z:Nesting.Tree.Plot (fork n f), Accept (X.r k) M η s z → ((X.r k)^(-(levy (fork n f):ℝ))≤B s) := by -- Plot notation type alias needs Nesting
            filter_upwards [X.drips.eventually (ge_mem_nhds zero_lt_one)] with k hk s z hz
            change _≤ toll (f:=f) (wages (stressTag U ab)) 0 0 s
            have hw : ∑i:(fork n f).Leaf,(wages (stressTag U ab) i) = (exponent (Leaf (fork n f)):ℝ):=by change ∑i:(fork n f).Leaf,(wages (stressTag U (I:=Leaf (fork n f)) ab) i) = _; simp [exponent, wages, degrees, stressTag]; ring
            unfold toll; rw [sub_zero,zero_sub, show s (.inl ()) = X.r k from hz.scale,hw]
            have hQ:=Measuring.Tree.tempered (hz.levels.mono le_rfl hk) one_pos
            apply le_mul_of_one_le_right (Real.rpow_nonneg (X.positive k).le _)
            refine Finset.one_le_prod (fun i hi=> Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hQ (.inr i)).1 ?_ ?_)
            · exact (Measuring.Tree.tempered (hz.levels.mono le_rfl hk) one_pos ..).2
            rw [sub_zero, neg_nonpos]; exact (Nat.cast_nonneg _).trans_eq (Measuring.Tree.head_cast (fork n f) _ _)
       let H:=Measuring.Tree.Nonroot f
       rcases isEmpty_or_nonempty H with he|he
       · refine ⟨1+A',add_pos_of_pos_of_nonneg zero_lt_one hA,?_⟩
         filter_upwards [hx,ht] with k hk ht s z hz hf
         have hC:=ht s z hz; specialize hk s z hz hf
         have hpos:0≤ B s:=(Real.rpow_nonneg (X.positive k).le _).trans hC
         refine ⟨(hk.1.trans ((mul_le_mul (le_add_of_nonneg_left zero_le_one) hC (Real.rpow_nonneg (X.positive k).le _) (le_of_lt (add_pos_of_pos_of_nonneg zero_lt_one hA))))),?_⟩
         rw [not_saving U R z p c D, sub_self,norm_zero]; apply mul_nonneg (by linarith only [hA])
         apply mul_nonneg hpos; change 0 ≤ ∑ x:H, (_ : ℝ); simp only [Fintype.sum_empty, le_rfl]
       obtain ⟨i⟩:=he; let gain:=b^(D (Sum.inr i)+1)
       let A:=1+(A'+A')/gain+A'
       have ha: (0:ℝ)<gain:=pow_pos hb _
       refine ⟨A,by unfold A; positivity,?_⟩
       filter_upwards [hx,ht] with k hk ht s z hz hf; apply And.intro
       · have hC:=ht s z hz; have hZ:= (hk s z hz hf).1.trans ((mul_le_mul_of_nonneg_left hC hA).trans (mul_le_mul_of_nonneg_right (by unfold A; linarith only [div_nonneg (add_nonneg hA hA) ha.le] : A' ≤ A) ((Real.rpow_nonneg (X.positive k).le _).trans hC)))
         exact hZ
       have hS : gain ≤ nestPrice s D :=by
           unfold nestPrice
           exact (pow_le_pow_left₀ hb.le (hf.2.2 i) _).trans (Finset.single_le_sum (f:=fun x:Measuring.Tree.Nonroot f=>(_root_.YM.OPE.Nesting.Tree.ratios (fork n f) 1 s (Sum.inr x))^(D (.inr x)+1)) (s:=Finset.univ) (fun u _=> by have hu:=hf.2.2 u; exact pow_nonneg (hb.le.trans hu) _) (Finset.mem_univ i))
       let r:=X.r k; let V:ℝ:=r^(-(levy (fork n f):ℝ)); let a:=A'
       have hp : 0 ≤ V:= Real.rpow_nonneg (X.positive k).le _
       have hP : a+a ≤ A*gain :=(div_le_iff₀ ha|>.1 (by unfold A; dsimp only [a,gain]; linarith only [hA]))
       calc _ ≤ A'*V + A'*V:=(norm_sub_le ..).trans (add_le_add (hk s z hz hf).1 (hk s z hz hf).2)
            _ ≤ (A*gain)*(B s) :=by rw [← add_mul]; exact mul_le_mul hP (ht s z hz) hp (mul_nonneg (by unfold A; positivity) ha.le)
            _ ≤ A*(B s)*nestPrice s D:=by rw [mul_assoc, mul_comm gain,←mul_assoc]; exact mul_le_mul_of_nonneg_left hS (mul_nonneg (by unfold A; positivity) (hp.trans (ht s z hz)))
            _ = _ := mul_assoc _ _ _
where not_saving(U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin){n:ℕ}{f:Fin n→Nesting.Tree}(z:Tree.Plot (fork n f))(p:(fork n f).Leaf→S.Tag)(i:R.channels 0)(D:(fork n f).Inner→ℕ)[h:IsEmpty (Measuring.Tree.Nonroot f)]:Kernel.chord U R z p i D=Kernel.output U R z p i := by
           let q:=Tree.still z
           have he(j):f j=bud:=by by_contra he; exact ((h.false) ⟨j,show _ from by cases hF:f j with
                     | bud =>exact (he hF).elim
                     | fork n f=> exact Sum.inl ()⟩) -- incorrect obtains
           exact (Composite.empty_gain U R (z:=q) (v:=p) D i he ()).trans (Limits.point_eq U R p i ())

end
section Results
include H h hM hη
lemma outright {m:ℕ}(c:R.channels m)(D:(fork n f|>.Inner)→ℕ)(ab:Picture (Leaf tree)){b:ℝ}(hb:0<b)(hD:∀ i:Measuring.Tree.Nonroot f,D (.inr i) ≤ 3)(hi:m<4):∃ A:ℝ,0 < A ∧ ∀ᶠ k in atTop,∀s:(fork n f).Inner→ℝ, ∀ z:(fork n f).Plot,Accept (X.r k) M η s z→ Flux s b →
    (let p:=stressTag U ab; let B:=toll (wages p) 0 m s; ‖Kernel.output U R z p c‖ ≤ A * B) ∧ ‖Kernel.output U R z (stressTag U ab) c -Kernel.chord U R z (stressTag U ab) c D‖ ≤ A * bothToll (wages (stressTag U ab)) 0 m D s:=by
           obtain h₀|h₀:=Nat.eq_zero_or_pos m
           · subst m; norm_num only [Nat.cast_zero]; exact outright_mid U R X h.simpleGate H h hM hη c D ab hb hD
           exact (no_channels U R X h.simpleGate h₀ hi|>.false c).elim
end Results

structure Partial : Prop where
    coefficients {n:ℕ}{f:Fin n→Nesting.Tree} (M η b:ℝ) (ab:Picture (_root_.YM.OPE.Nesting.Tree.Leaf (Nesting.Tree.fork n f))) (D:Nesting.Tree.Inner (Nesting.Tree.fork n f)→ℕ){m:ℕ}(i:R.channels m): 0 ≤ M → 0 < η → 0 < b → (∀ i:Measuring.Tree.Nonroot f,D (.inr i) ≤ 3) → m < 4 → ∃ A:ℝ,0 < A ∧ ∀ᶠ k in atTop,∀s:(fork n f).Inner→ℝ, ∀ z:(fork n f).Plot,Accept (X.r k) M η s z→ Flux s b → let p:=stressTag U ab; let B:=toll (wages p) 0 m s; ‖Kernel.output U R z p i‖ ≤ A * B ∧ ‖Kernel.output U R z p i-Kernel.chord U R z p i D‖ ≤ A * bothToll (wages p) 0 m D s
    tests {n : ℕ}{f : Fin n→Nesting.Tree} {v:(fork n f).Leaf→S.Tag}{J:Type}[Fintype J](w:J→ S.Tag)(M η δ:ℝ)(A:ℝ)(D:ℕ): 0 ≤ M → 0 < η →0 < δ →0 ≤ A → D≤2→ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→ E4,Accept x M η s z→ Buffer z y δ →Large.Moderated x s A → let b:=toll (wages v) 0 (D+1:ℕ) s; ‖Kernel.normData U R z v D y w‖ ≤ b ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q D y w‖ ≤ b
    matchStress {I : Type}[Fintype I](d:Picture I) {M η:ℝ}: 0 ≤ M → 0 < η → ∀ ε>0, ∀ᶠ k in atTop,∀ x∈plate I M η,∀ o:E4,
      ‖(↑((X.r k)^(exponent I)) :ℂ) * scalar U R (harmonic (X.r k) x o) (stressTag U d) o-meter (C:=C) d x‖≤ε ∧ ∀ q:Viewers U, ‖(↑((X.r k)^(exponent I)) :ℂ) * Orbits.moment (spectator U q) (harmonic (X.r k) x o) (voices (stressTag U d)) - meter (C:=C) d x‖≤ε
include h H
lemma wave : Partial U R X :=by
    constructor
    · intro n f M η b ab D m c hm hη hb hd ht
      exact outright U R X H h (ab:=ab) (D:=D) (c:=c) hm hη hb hd ht
    · intro n f v J hJ w M η δ a d hM hη hδ ha hd
      exact Large.residue U R X h.simpleGate v a ha d hd w h hM hη hδ
    intro I hI ab M η hM hη ε he
    exact predicts U R X h.simpleGate H ab hM hη h he
end YM.OPE.Short
namespace YM.OPE.Short
open Orbits Function Set Table Extraction Pert
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
theorem rooted (G:Gauge)(hG:G.Simple)(f:Order):∃ (C:Family G) (g:Order) (S:Table C.book), Services C (f.refine g) S ∧ ∃ (U:Spec.Final C (f.refine g) S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (X:Climb.Scaling S), Foundation U R ∧ Nesting.Uniform U R ∧ Sparse.Quiet U R ∧ FirstExtension U X ∧ Partial U R X :=by
    obtain ⟨C,g,S,h,U,R,h',hT,hB,X,hh,hS⟩:=Sparse.rooted G hG f
    exact ⟨C,g,S,h,U,R,X,hB,hT,h',hh,wave U R X hh h⟩
end YM.OPE.Short
