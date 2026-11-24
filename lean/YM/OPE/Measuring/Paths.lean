import YM.OPE.Measuring.Joined
import YM.OPE.Measuring.Grams
import YM.OPE.Measuring.Germs

/-! Joint endpoint through the free comparison and regular case of the
power-log requests, staying on Spec.Final of strengthened F3 single start.
Not a replacement of that witness by a purely regular theory. The absent
singular fusions in this special case would be essential in the full application. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring
open Orbits Orbits.Reader Nesting Function Filter Set Table Next.UVStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)

structure Scoop : Prop where
    exact_path {n:ℕ}{f:Fin n→Nesting.Tree}{M η:ℝ} (ht:Tree.Narrow (Tree.Fork f))(hm:0≤M)(hη:0<η)(v:(Nesting.Tree.fork n f).Leaf→S.Tag){d:ℕ}(j:R.channels d)(D:(Nesting.Tree.fork n f).Inner→ℕ):
       ∃ K:ℝ, 0 < K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(Nesting.Tree.fork n f).Inner→ℝ,∀ z:(Nesting.Tree.fork n f).Plot, Accept x M η s z → ‖Kernel.output U R z v j‖ ≤ K*Nesting.Tree.toll (wages v) 0 d s ∧ ‖Kernel.output U R z v j-Kernel.chord U R z v j D‖ ≤ K*Nesting.Tree.bothToll (wages v) 0 d D s
    exact_tested {n:ℕ}{f:Fin n→Nesting.Tree}{M η δ:ℝ} (ht:Tree.Narrow (Tree.Fork f))(hm:0≤M)(hη:0<η)(v:(Nesting.Tree.fork n f).Leaf→S.Tag)
      {J:Type}[Fintype J](w:J→S.Tag)(hδ:0 < δ) (D:ℕ):∃ K:ℝ, 0 < K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ (s:(Nesting.Tree.fork n f).Inner→ℝ)(z:(Nesting.Tree.fork n f).Plot) (y:J→ E4),Accept x M η s z→ Buffer z y δ →
    Injective (beside (z ∘ (Nesting.Tree.fork n f).leafSeat) y) ∧ Injective (beside (sole (Nesting.Tree.anchor z)) y) ∧ ‖Kernel.normData U R z v D y w‖ ≤ K*Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q D y w‖ ≤ K*Nesting.Tree.toll (wages v) 0 (D+1:ℕ) s

include h
lemma scoop : Scoop U R where
    exact_tested :=by intro n f M η δ ht hm hη v J hJ w hδ D; exact Germ.residual U R h v hm hη ht w hδ D
    exact_path := by
      intro n f M η ht hm hη v d j D
      obtain ⟨A,hA,hg⟩:=Germ.direct U R h v hm hη ht j D
      obtain ⟨B,hB,hg'⟩:=Germ.compare U R h v hm hη ht j D
      refine ⟨max A B, hA.trans_le (le_max_left ..),?_⟩
      filter_upwards [hg,hg'] with x hx hx' s z hz
      have hn(i:(Nesting.Tree.fork n f).Inner):0 ≤ s i:=hz.levels.positive i|>.le
      have hr :(0:ℝ) ≤ Nesting.Tree.toll (wages v) 0 (↑d:ℝ) s := mul_nonneg (Real.rpow_nonneg (hn (.inl ())) _) (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (Tree.whole_offset.ratio_pos one_pos (fun i=>hz.levels.positive (i: (Nesting.Tree.fork n f).Inner)) (.inr i) |>.le) _))
      exact And.intro (hx s z hz |>.trans (mul_le_mul_of_nonneg_right (le_max_left A B) hr)) (hx' s z hz |>.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (mul_nonneg hr (Finset.sum_nonneg fun j _=>pow_nonneg (Tree.whole_offset.ratio_pos one_pos (fun i=>hz.levels.positive i) (Sum.inr j:(Nesting.Tree.fork n f).Inner) |>.le) (D (Sum.inr j)+1)))))
omit h U R in
theorem paths (G:Gauge)(hg:G.Simple):∃ C:Family G, Extraction.Wcmain C ∧ ∀ f:Extraction.Order, ∃ (g:Extraction.Order) (S:Table C.book), Services C (f.refine g) S ∧ ∃ (U:Spec.Final C (f.refine g) S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (X :_root_.YM.Climb.Scaling S), Nonempty {a : (Climb.Bel C.book).Hierarchy // ∀ d, ∃ s K,1 ≤ K ∧ ∀ᶠ k in atTop,∀ x:S.Field d,
   ‖(X.U k d).symm x‖ ≤ K*‖checks U X s k d x‖ ∧ ‖checks U X s k d x‖ ≤ K*‖(X.U k d).symm x‖} ∧ Pert.FirstExtension U X ∧ Uniform U R ∧ Foundation U R ∧ Approaches (path X) (isoPanel X) ∧ Scoop U R := by
      obtain ⟨C,_,hc,h'⟩:=simultaneous G hg 1 one_pos
      obtain ⟨M,⟨hT⟩⟩:=Maxwell.Free.maxwell_supplies C hg 1 one_ne_zero
      refine ⟨C,hc,fun f=>?_⟩
      obtain ⟨g,S,h,U,R,X,h1,h2,h3,h4⟩:=h' f
      exact ⟨g,S,h,U,R,X,⟨⟨M.hT,weak_probe U X h4 M.hT⟩⟩, h1,h2,h3,h4,scoop U R h⟩
end YM.OPE.Measuring
