import YM.OPE.Measuring.Corners

/-!
# Actual epsilon-free finite nesting bounds on regular elementary paths

Special case where every fork has at most one child. Includes arbitrary labels
in that slot, arity/depth and finite intermediate horizons, arbitrary ratios
(no positive lower bound). Does not evaluate a general two-leaf product at
coincidence. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Germ
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Measures Menu Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
variable {n:ℕ}{f:Fin n→Tree}
local notation "tree" => (Measuring.Tree.Fork f)
variable (v:(fork n f).Leaf→S.Tag){M η:ℝ}(hM:0≤M)(hη:0<η)(ht:Measuring.Tree.Narrow (Measuring.Tree.Fork f))
include h hM hη ht
private lemma toll (d:Bool){m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ):
  ∃ C:ℝ, 0<C ∧
    ∀ᶠ x:ℝ in 𝓝[>]0,∀ s z, Accept x M η s z → let g:=Kernel.output U R z v c; ‖ite d (g-Kernel.chord U R z v c D) g‖ ≤ C*_root_.YM.OPE.Nesting.Tree.toll (wages v) 0 m s * Measuring.Tree.allowance d D ((fork n f).ratios 1 s) := by
    let g (z : Nesting.Tree.Plot tree):=Kernel.output U R z v c; let f(z):= Kernel.chord U R z v c D
    let F (z):=ite d (g z - f z) (g z)
    refine Measuring.Tree.restore (m:=m) F d D (degrees v) ht hM ?_ (Measuring.Tree.smooth_plot U R v c D d ht) ?_
    · intro z a; unfold F g f; rw [Measuring.Tree.output_carry U R, Measuring.Tree.chord_carry U R]
    intro μ hμ ε hε; unfold F Measuring.Tree.allowance
    filter_upwards [(uniform U R h).direct _ _ v m c D μ η ε hμ hη hε] with x hx s z hz
    obtain ⟨-, -, hg, hf⟩:=hx s z hz; split_ifs
    · exact hf
    rw [mul_one]; exact hg

lemma direct {m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ):
    ∃ C:ℝ, 0<C ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z → ‖Kernel.output U R z v c‖ ≤ C*Nesting.Tree.toll (wages v) 0 m s:=by
      obtain ⟨k,hk,hg⟩:=toll U R h v hM hη ht false c D
      exact ⟨k,hk,hg.mono fun x hx s z h=>by simpa [Measuring.Tree.allowance] using hx s z h⟩
lemma compare {m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ):
    ∃ C:ℝ, 0<C ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z → ‖Kernel.output U R z v c-Kernel.chord U R z v c D‖ ≤ C*Nesting.Tree.bothToll (wages v) 0 m D s:=by
      obtain ⟨k,hk,hg⟩:=toll U R h v hM hη ht true c D
      exact ⟨k,hk,hg.mono fun x hx s z h=>by simpa [Measuring.Tree.allowance,bothToll,nestPrice,mul_assoc] using hx s z h⟩

omit ht hM hη
section Exterior
variable {J:Type}[Fintype J]
lemma viewer_bounded {m:ℕ}{δ:ℝ}(hδ:0<δ)(c:S.Field m)(w:J→S.Tag):
    ∃ B:ℝ,∀(o:E4) (y:J→E4)(i:Viewers U), Buffer (sole o) y δ → ‖Orbits.whole (spectator U i) (sole o) (sole c: Labels S (fun _:Unit=>m)) y (voices w)‖ ≤ B:=by
    by_contra! hg
    let T (n:ℕ):ℝ:=n
    have hT:Tendsto T atTop atTop:=tendsto_natCast_atTop_atTop
    choose o y i ho hφ using fun n:ℕ => hg (Real.exp (1*T n))
    have h1 : Kept atTop T 0 (sole ∘ o):=Kept.sole atTop T o 0
    obtain ⟨h₁,h₂⟩:=Limits.buffer_stage hT hδ (Eventually.of_forall ho)
    have h':=viewer_cost U h.schedule (Orbits.names (sole c : Labels S (fun _:Unit=>m))) (names (voices w)) hT i h1 h₂ h₁ le_rfl le_rfl
    simp only [mul_zero,add_zero] at h'
    obtain ⟨t,ht⟩:= (h' 1 zero_lt_one).exists
    exact (lt_of_le_of_lt ht (by simpa only [Orbits.whole_observed,Function.comp_apply] using hφ t)).false

omit h
variable (w:J→S.Tag)
private lemma push (z:(fork n f).Plot){y:J→E4}{r:Viewers U}(m:ℕ):
    Kernel.pipe U R z v r m y w= Kernel.pipe U R z v r (m+1) y w + ∑ c:R.channels (m+1),Kernel.output U R z v c*Orbits.whole (spectator U r) (sole (anchor z)) (sole (R.actor (m+1) c):Labels S (fun _:Unit=>m+1)) y (voices w) := by
    unfold Kernel.pipe Orbits.formula Orbits.trunc; conv_rhs => arg 1; arg 2; rw [Fin.sum_univ_castSucc]
    change (?a:ℂ) - ?b = ?a - (?b + ?K) + ?K
    abel

private lemma strict_root {x:ℝ}{s:(fork n f).Inner→ℝ}{z:(fork n f).Plot}(hg:Accept x M η s z)(D:ℕ): x^((D+1:ℕ)-weight (degrees v)) ≤ Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s:=by
    unfold Nesting.Tree.toll; rw [sub_zero]
    -- no inner-root excess needed
    have hx:s (.inl ())=x:=hg.scale
    rw [hx]; apply le_mul_of_one_le_right (by exact Real.rpow_nonneg ((hg.levels.positive _).le.trans_eq hx) _) (Finset.one_le_prod fun j _=>?_)
    -- ratios≤1, induction as tempered with outer parent =?_ ; x not <1! only nonroot
    change 1 ≤ ((f j.fst).ratios (s (Sum.inl ())) (Nesting.Tree.childAge j.fst s) j.snd)^((-headSum (fork n f) (wages v) (.inr j)-0:ℝ))
    obtain ⟨h₁,h₂⟩:= Measuring.Tree.tempered (t:=f j.fst) (p:=s (.inl ())) (by simpa using hg.levels.2.2 j.fst) (hg.levels.positive _) j.snd
    have ht:= Measuring.Tree.head_cast (fork n f) (degrees v) (.inr j)
    rw [sub_zero,show headSum (fork n f) (wages v) (Sum.inr j)= (Tree.headNat (fork n f) (degrees v) (.inr j):ℝ) from ht.symm]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h₁ h₂ (by
       exact neg_nonpos.mpr (Nat.cast_nonneg _))
include h hM hη ht
lemma residual {δ:ℝ}(hδ:0 < δ) (D:ℕ):∃ C:ℝ, 0 < C ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:(fork n f).Plot) (y:J→ E4),Accept x M η s z→ Buffer z y δ →
    Injective (beside (z ∘ (fork n f).leafSeat) y) ∧ Injective (beside (sole (anchor z)) y) ∧ ‖Kernel.normData U R z v D y w‖ ≤ C*Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q D y w‖ ≤ C*Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s:=by
       choose B hB using fun c:R.channels (D+1)=>viewer_bounded U h hδ (R.actor (D+1) c) w
       choose A hA hZ using fun c:R.channels (D+1)=>direct U R h v hM hη ht c (fun _=>D+1)
       let K:ℝ:=1+∑ c:R.channels (D+1),A c * max (B c) 1; have hK:0<K:=zero_lt_one.trans_le (le_add_of_nonneg_right (Finset.sum_nonneg fun j _=>mul_nonneg (hA j).le (zero_le_one.trans (le_max_right ..))))
       refine ⟨K,hK,?_⟩
       have hH:= Orbits.quantitative_separated U R h (voices v) (voices w) hM hη (ε:=1/2) (by norm_num) (D+1) hδ
       filter_upwards [hH,eventually_all.mpr hZ,eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx h_i h' s z y hg hy
       have hp:0<x:=(hg.levels.positive _).trans_eq hg.scale
       let r:=Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s
       have hClear: ClearOf (anchor z) y δ:=⟨fun j=>hy.1 (fork n f|>.topSeat) j,hy.2⟩
       have hSpan:WithinRoom x M η (Nesting.Tree.profile z) (anchor z):= ⟨fun j=>by exact le_trans (hg.relative.from_current _) (congr_arg (M*·) hg.scale).le,fun i j hj=> (hj ((Measuring.Tree.leaf_sub ht).allEq i j)).elim⟩
       obtain ⟨hxy,hoy,_,hZ⟩:=hx (Nesting.Tree.profile z) (anchor z) y hSpan hClear -- fix
       have htq:=strict_root v hg D
       have hr:0 ≤ r:=(Real.rpow_nonneg hp.le (_:ℝ)|>.trans htq)
       have hi(i) := show ‖Kernel.pipe U R z v i D y w‖ ≤ K*r from (?_)
       refine ⟨hxy,hoy,glance_contract U (mul_nonneg hK.le hr) |>.mpr (fun q=>by rw [Kernel.normData,Orbits.formula_seen _ _ _ _ _ _ _ _ _ hxy hoy]; exact hi q),hi⟩
       rw [push U R v w z D]; 
       have he(i): ‖Orbits.formula U R (Nesting.Tree.profile z) (anchor z) (voices v) y (voices w) (D+1) i‖ ≤ x^((D+1:ℕ)-weight (degrees v)):= (hZ i).trans (Real.rpow_le_rpow_of_exponent_ge hp h' (by linarith only)) -- ensure Nat cast simplification
       let g(j:R.channels (D+1)):= Kernel.output U R z v j*Orbits.whole (spectator U i) (sole (anchor z)) (sole (R.actor (D+1) j):Labels S (fun _:Unit=>D+1)) y (voices w)
       let a c:=A c*max (B c) 1
       refine (norm_add_le ..).trans ?_; exact (add_le_add (he i|>.trans htq) (show ‖∑j, g j‖ ≤ ∑ j:R.channels (D+1), a j*r from (norm_sum_le _ g).trans (Finset.sum_le_sum (g:=fun c=>a c*r) fun c _=> (by
           change ‖g c‖ ≤ _
           calc _ ≤ _ := norm_mul_le ..
                _ ≤ A c*r*max (B c) 1 := (mul_le_mul (h_i c s z hg) ((hB c (anchor z) y i ⟨fun _ b=>hy.1 (fork n f|>.topSeat) b,hy.2⟩).trans (le_max_left ..)) (norm_nonneg ..) (mul_nonneg (hA c).le hr))
                _ = _ := by unfold a; ring)))).trans_eq (by change r + (∑ c,a c * r) = (1+∑ c,a c)*r; rw [add_mul,one_mul,sum_mul])
end Exterior
end YM.OPE.Measuring.Germ
