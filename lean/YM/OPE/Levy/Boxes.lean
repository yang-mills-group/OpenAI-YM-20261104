import YM.OPE.Levy.Measured

/-! Prices in fixed separated shapes on the stationary sequence. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.OPE.Levy
open Filter Set Function Table Ward Orbits Extraction Climb Next.UVStress Spec
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S) (H:Anchored U.sector.derivatives (path X) (isoPanel X)) (h₀:Services C F S)
local notation "Q" =>U.sector.derivatives
local notation "T" =>zstamp (path X)
local notation "A" =>X.U
local notation "r" =>X.r

variable {I J:Type}[Fintype I][Fintype J](x:ℕ→I→E4)(o:ℕ→E4)(y:ℕ→J→E4){M η δ:ℝ}
  (hη:0 < η)(hδ:0 < δ)(hx:∀ k,WithinRoom (X.r k) M η (x k) (o k))
  (hy:∀ k,ClearOf (o k) (y k) δ)
lemma stamp_radius(i:ℕ): T i= -Real.log (X.r i):=rfl

include X hη hx
lemma stamps: enveloped atTop T 1 x o ∧ Kept atTop T 1 x:=by
      have hq:Tendsto (zstamp (path X)) atTop atTop:=zlarge (path X)
      have hr:RateIs atTop (zstamp (path X)) X.r (-1) :=(RateIs.exp (-1) hq).congr <| Eventually.of_forall fun i=>by change Real.exp ((-1:ℝ)*zstamp (path X) i)= X.r i; rw [stamp_radius,neg_one_mul,neg_neg,Real.exp_log (X.positive i)]
      constructor
      · have h':=((RateLE.const (max 0 M) hq).mul (hr.pays hq))
        rw [zero_add] at h'
        refine h'.norm.transfer (G:=fun i=>away (x i) (o i)) (Eventually.of_forall fun i=>?_ )
        · rw [norm_norm]; apply le_trans ((_ : ‖away (x i) (o i)‖ ≤ max 0 M * X.r i)) (Real.le_norm_self _)
          apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_max_left ..) (X.positive i).le)).2
          exact fun j => le_trans ((hx i).span _) (mul_le_mul_of_nonneg_right (le_max_right ..) (X.positive i).le)
      intro b hb
      let s:=fun k=>Real.exp (-b*T k)
      have he : RateLE atTop T s (-b) := RateLE.exp _ hq
      have hW:= (RateIs.const hq hη).mul hr |>.overtakes he hq (by linarith only [hb])
      filter_upwards [hW] with i hi j k hj
      exact lt_of_lt_of_le hi ((hx _).spaced j k hj)

omit hx hη
include hy hδ
lemma static: Intervals atTop T 0 (sole ∘ o) y ∧ Kept atTop T 0 y:=by
     have hs(a:ℝ)(h:0<a):∀ᶠ k in atTop, Real.exp (-a*T k) < δ :=(zlarge (path X)).eventually ((Real.tendsto_exp_atBot.comp ((Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr h) (tendsto_id (α:=ℝ))))).eventually (gt_mem_nhds hδ))
     constructor
     · intro a ha; filter_upwards [hs a ha] with i hi j k using lt_of_lt_of_le hi (ClearOf.openSpace (hy _) _)
     intro a ha; filter_upwards [hs a ha] with i hi j k hj using lt_of_lt_of_le hi ((hy _).spread j k hj)

include hx hη
variable {d:I→ℕ}{e:J→ℕ} (v:(i:I)→(Bel C.book).Field (d i))(w:Labels S e) (D:ℕ)
include U h₀ H

lemma in_boxes(q:ℕ→Viewers U) :RateLE atTop T (residual U R X v w x y o q D) (-(D+1:ℝ)):=by
     obtain ⟨h₁,h₂⟩:=stamps X x o hη hx
     obtain ⟨h₃,h₄⟩:=static X o y hδ hy
     convert residual_rate U R X H h₀ v w x y o q D h₁ h₂ h₃ h₄ (le_refl (0:ℝ)) (le_refl (0:ℝ)) zero_lt_one using 1; ring

omit hx hy
lemma uniform (b:ℝ)(hb:-(D+1:ℝ)< b):∀ᶠ k in atTop,∀ (q:Viewers U) (x:I→E4)(o:E4)(y:J→E4),WithinRoom (X.r k) M η x o → ClearOf o y δ →
              ‖Orbits.balance U (spectator U q) R D x o (primary X d v k) y w‖ ≤ Real.exp (b*T k):=by
      let Z k:= {p : Loc I J | WithinRoom (X.r k) M η p.1 p.2.1 ∧ ClearOf p.2.1 p.2.2 δ}
      by_cases h: ∀ k,(Z k).Nonempty
      · have (k:ℕ) : Nonempty ((Z k)×Viewers U):= ⟨⟨(h k).some,(h k).some_mem⟩,Classical.arbitrary _⟩
        have he : ∀ᶠ k in atTop, ∀ (z:Z k × Viewers U), ‖Orbits.balance U (spectator U z.2) R D z.1.val.1 z.1.val.2.1 (primary X d v k) z.1.val.2.2 w‖ ≤ Real.exp (b*T k):=by
          apply dependent_all (l:=atTop) (V:=fun k=> (Z k)×Viewers U)
          intro f
          exact in_boxes U R X H h₀ (fun k=>(f k).1.val.1) (fun k=>(f k).1.val.2.1) (fun k=>(f k).1.val.2.2) hη hδ (fun k=>(f k).1.property.1) (fun k=>(f k).1.property.2) v w D (fun k=>(f k).2) b hb
        filter_upwards [he] with k hk q x o y hx hy using hk (⟨⟨x,o,y⟩,hx,hy⟩,q)
      push Not at h
      obtain ⟨t,ht⟩:= h
      apply Eventually.of_forall
      intro i q x o y hx he
      let p':Loc I J:=⟨fun j=>(X.r t / X.r i) • (x j-o)+o,o,y⟩
      have hpos:0 < (X.r t) / X.r i:=div_pos (X.positive _) (X.positive _)
      have ha: p'∈ Z t:=by
           constructor
           · constructor
             · intro j; simp only [p',add_sub_cancel_right,norm_smul_of_nonneg hpos.le]
               exact ((mul_le_mul_of_nonneg_left (hx.span j) hpos.le).trans (le_of_eq (by field_simp [(X.positive i).ne'])))
             intro j l hj; simp only [p',add_sub_add_right_eq_sub, ← smul_sub, sub_sub_sub_cancel_right, norm_smul_of_nonneg hpos.le]; apply le_trans _ (mul_le_mul_of_nonneg_left (hx.spaced _ _ hj) hpos.le); apply le_of_eq; field_simp [(X.positive i).ne']
           exact he
      exact ((Set.eq_empty_iff_forall_notMem.mp ht p') ha).elim
where
  dependent_all {α:Type}{l:Filter α}{V:α→Type}[∀ k,Nonempty (V k)]{p: ∀ i, V i→Prop}(h:∀ f:(k:α) → V k,∀ᶠ i in l, p i (f i)):∀ᶠ i in l, ∀ v:V i, p i v:=by
    let f:=fun i=>if h:∃ v, ¬p i v then h.choose else Classical.arbitrary _
    filter_upwards [h f] with i hi v
    unfold f at hi
    split at hi
    next hv=> exact (hv.choose_spec hi).elim
    next hv=>exact Classical.byContradiction (fun h'=>hv ⟨_,h'⟩)

end YM.OPE.Levy
