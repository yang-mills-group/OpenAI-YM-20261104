import YM.MS.Class.Kinetic
import YM.MS.Class.Pair
/-! Rank two identities, $Q c A$ eliminates longitudinal symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect.Mark
open Function Filter Set Finset Plane Koszul Real Momentum Wire LogTime
open scoped Topology ContDiff
open Complex (I)
variable {G: Gauge} {F : Law G} {h : ℤ} (i j : CI G)

lemma transverse (X:Class F h) (hx:h≤4) (a:Axis) (p:FourP): ∑ k:Axis, (p k:ℂ)*kinPair F i j k a p=0:=by
    obtain ⟨b,_,hb⟩:= ghost_scalar i j X hx
    have hv := X.closed [C i p,W a j (-p)] (by simp [C,W,qnote,net]); rw [qGhost,qAA] at hv; simp_rw [at_D,q0,add_zero] at hv
    let Y:= ∑ k:Axis, -(precision k a (-p):ℂ)* ghostPair F i j k p
    have ht : Y=0:= by
       unfold Y; simp_rw [hb,k_even,neg_mul]; rw [Finset.sum_neg_distrib]; suffices H: ∑ x:Axis,(precision x a p:ℂ)*((b:ℂ)*I*(p x:ℂ))=0 by rw [H]; simp
       have hq k : (precision k a p:ℂ)*((b:ℂ)*I*(p k:ℂ))=(b:ℂ)*I*((precision k a p:ℂ)*(p k:ℂ)):= by ring
       simp_rw [hq,← Finset.mul_sum,czero,mul_zero]
    change ((∑ k:Axis,I*(p k:ℂ)*kinPair F i j k a p) - Y=0) at hv
    simp_rw [ht,sub_zero,mul_assoc,← Finset.mul_sum] at hv; exact (mul_eq_zero.mp hv).resolve_left Complex.I_ne_zero
lemma diag_spectrum {B : ℂ} {a:Axis} (X:Class F h) (hx:h≤4) (hB : ∀ k,k ≠ a → ∀ p,kinPair F i j k a p=(precision k a p:ℂ)*B) :
    ∀ p, kinPair F i j a a p = (precision a a p:ℂ)*B:= by
    let L:= fun p=> kinPair F i j a a p - (precision a a p:ℂ)*B
    have ht : ∀ p:FourP, p a≠0 → L p=0:= by
       intro p hp; have he:= transverse i j X hx a p
       have H : ∑ k:Axis,(p k:ℂ)*((precision k a p:ℂ)*B)=0:= by simp_rw [← mul_assoc,mul_comm (p _:ℂ) (precision _ _ _:ℂ),← Finset.sum_mul, czero, zero_mul]
       have hx (k) (h:k≠a): (p k:ℂ)*(kinPair F i j k a p-(precision k a p:ℂ)*B)=0:= by rw [hB k h p,sub_self,mul_zero]
       have U : (p a:ℂ)*L p=0:= by dsimp only [L]; rw [← Finset.sum_eq_single a (fun j hj he=> hx j he) (fun hj=> (hj (mem_univ _)).elim)]; simp_rw [mul_sub, Finset.sum_sub_distrib,he,H,sub_self]
       exact (mul_eq_zero.mp U).resolve_left (by exact_mod_cast hp)
    intro p
    apply sub_eq_zero.mp
    by_cases hp:p a=0
    · let c (t:ℝ) := p+t • spike a; have hc : Filter.Tendsto c (𝓝[≠] 0) (𝓝 p):= by
        have h0 : Continuous c:= by unfold c; fun_prop
        have hv : c 0=p:= by simp [c]
        exact Filter.Tendsto.mono_left (show Filter.Tendsto c (𝓝 0) (𝓝 p) from hv ▸ h0.continuousAt) nhdsWithin_le_nhds -- maybe stuck
      have hl : Continuous L:= (kshape X i j a a).smooth.continuous.sub (by unfold precision delta Momentum.sq; simp only [↓reduceIte]; fun_prop)
      have hr : Filter.Tendsto (L ∘ c) (𝓝[≠] 0) (𝓝 0):= by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht0; have hq : t≠0:=by simpa using ht0
          exact Eq.symm (ht (c t) (by simp [c,hp,hq]))
      exact tendsto_nhds_unique ((hl.tendsto p).comp hc) hr
    exact ht p hp


-- Determine common offdiag coefficient just by H symmetry.
lemma eigsame (X:Class F h) {a b u v : Axis} (hx:a≠b) (hy:u≠v): kinPair F i j a b (spike a+spike b)=kinPair F i j u v (spike u+spike v):= by
    obtain ⟨f,hf,hu⟩:= perm2 a b u v hx hy; have ht:= ksign i j X (orient f) a b (spike a+spike b); simpa [orient, hf,hu] using ht.symm
lemma spectrum (X:Class F h) (he:h≤4) : ∃ b:ℝ, (h=4 ∨ b=0) ∧ ∀ a k p, kinPair F i j a k p=(precision a k p:ℂ)*(b:ℂ):=by
   suffices H : ∃ b:ℝ,(h=4 ∨ b=0)∧ ∀ a k,a≠k→∀ p, kinPair F i j a k p=(precision a k p:ℂ)*(b:ℂ) by
      obtain ⟨b,hb,H⟩:=H
      refine ⟨b,hb,fun a k p=>?_⟩; by_cases hv:a=k
      · subst a; exact diag_spectrum i j X he (fun j hv=> H j k hv) p
      exact H a k hv p
   have hz a k:= kshape X i j a k
   by_cases hh:h=4
   · obtain ⟨b,hb⟩:= evenStar (kinPair F i j 0 1 (spike 0+spike 1)) (by
        let p:=spike 0+spike 1; apply Eq.trans (even i j X 0 1 p).symm
        convert! X.solid.real' [W 0 i p,W 1 j (-p)] (fun _=>by simp [W,net,qnote]) using 1)
     subst h; refine ⟨-b, Or.inl rfl,fun a k h p=>?_⟩
     rw [shape_skew_two h (hz a k) (oddtwo i j X h) (oddtwo' i j X h), eigsame i j X h (show (0:Axis)≠1 by decide), hb,precision,delta]; simp [h]
   refine ⟨0, Or.inr rfl,fun a k hp p=>?_⟩; simp only [Complex.ofReal_zero,mul_zero]
   rcases lt_trichotomy h 2 with h1|h1|h1
   · rw [(hz a k).charge (by omega)]; rfl
   · subst h; rw [shape_constant (hz a k) p]; exact unstuck (oddtwo i j X hp) 0 rfl
   have hi : h=3:= by omega
   subst h; refine skew_null _ ?_; have he:= (hz a k).scale (-1) p; norm_num at he; exact (even i j X a k p).symm.trans he

end YM.MS.Landau.Detect.Mark
