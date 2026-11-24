import YM.Push.STRESS_FLUX.Counts
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank
import YM.FrontierTrace.Shear.Leading

/-!
# No quotient at W4

Every projection-map coefficient can be read before quotient. For the *same* F
and all real stencils, providing leading forests for A and formal tests. DOES
NOT claim continuation between horizons or that the actual bare Action stencil
itself is in this collection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Labels Analysis Maxwell UVNext.FreeStress StressFlux Extra.FD
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}

lemma surj0 : Surjective (gaugeJet (j:=0) (G:=G)):=by
   intro x; let w:= potential x; have he: w.val ∈ onShell G.Color 0:=by
      refine ⟨w.property,fun b y=>?_⟩
      apply Finset.sum_eq_zero; intro i _; let k:= w.val i b
      have hk : Tensor.diagonal k=fun _=> Tensor.diagonal k 0:=funext (fun _=> congr_arg k (Subsingleton.elim ..))
      change grad i (Tensor.diagonal k) y=0; rw [hk]; simp [grad,D]
   exact ⟨⟨w.val,he⟩,potential.symm_apply_apply x⟩

/-- No degree<5 free EOM, all gauge-invariant Label coefficients inject. -/
lemma ideal0 (h:G.Simple){d} (hd:d≤4): equationIdeal G d = ⊥:= by
   apply bot_unique; intro p hp; change p=0
   obtain ⟨A,hA,hB,h⟩:= StressFlux.low (Nat.le_trans hd (by decide)) p
   have hc:=StressFlux.Low.covariance hA h
   apply StressFlux.label_ext; intro J
   obtain ⟨x,hx⟩:= surj0 (J 0)
   let B: TaylorTower G:= Pi.single 0 x
   have hx': gaugeJet (B 0)=J 0:= by unfold B; rwa [Pi.single_eq_same]
   have hv:= ideal_meaning.mp hp B
   rw [h, Low.eval,(A.linear_invariant ‹G.Simple› hc), hB hd, hx'] at hv
   rw [h,Low.eval,A.linear_invariant ‹G.Simple› hc,hB hd]; simpa using hv

/-- Whole label basis, not just independent-test pivots; nonredundant.
At 5 the statement fails for free, `StressFlux.eom`. -/
lemma projected4 (L: Frames G)(h:G.Simple){d}(hd:d≤4): Injective ((freeTable L).project d) := by
   let P:= exactField L d
   intro x y he; have heq:=congr_arg P he; dsimp only [P] at heq; simp only [exact_project] at heq
   refine (L.level d).coords.symm.injective ((LinearMap.ker_eq_bot.mp (show (observable G d).ker = ⊥ from ideal0 h hd)) ?_)
   exact congr_arg Subtype.val heq

lemma actual_projection {C:Family G}{S:Table C.book}{d}(Z : Spin.change S d) (h:G.Simple)(hd:d≤4) : Bijective (S.project d):=by
   let U := Climb.Bel C.book; let L:= LinearEquiv.ofBijective ((freeTable C.labels).project d) ⟨projected4 _ h hd,(freeTable C.labels).onto d⟩
   let B := (L.trans Z)
   refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr (S.onto d), S.onto d⟩; exact B.finrank_eq

open Next.UVStress
lemma no_eom4 {C:Family G}{S:Table C.book}{d}(Z : Climb.Scaling S) (h:G.Simple)(hd:d≤4) : S.null d=⊥ := by
   have he := (LinearMap.ker_eq_bot.mpr (actual_projection (Z.U 0 d) h hd).1)
   rw [show S.project d=(S.null d).mkQ from rfl, Submodule.ker_mkQ] at he; exact he

/-- Unit in every fiber. Actual C.refUnit already built; depends on ref d.
 Exact term distinct from free table one once unit and label fibers coerce. -/
lemma unit_label (G:Gauge) (C:Family G) (d:ℕ) : C.book.scalar d= C.refUnit d:=by
   rfl

lemma bond_at (G:Gauge) (i j a b:Axis) : ff G 4 le_rfl i j a b = pair G i j a b:=by
   apply label_ext; intro J; rw [pair_value]; change read J (tape ..)= _
   rw [eval_tape]; apply congr_arg ((↑):ℝ→ℂ); congr 1
   · exact congr_arg (takeCurl (J 0) i j) (Subsingleton.elim ..)
   exact congr_arg (takeCurl (J 0) a b) (Subsingleton.elim ..)

end YM.FrontierTrace.Primary
