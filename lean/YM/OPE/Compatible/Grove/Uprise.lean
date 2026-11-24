import YM.OPE.Compatible.Grove.Bloom
/-! # Density before tower. Raw purchases at unfolded every torus believed by expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
-- no silt yet. fees
abbrev exactAtoms (A:I→ Atom G n)(u: Signed):= rhythm (smelt A u) (brass A)
abbrev paymentAtoms (A:I→ Atom G n)(u:Signed)(r:ℕ):= timbre (smelt A u) (brass A) r
lemma emp (I:Type*)(G:Gauge)(n r:ℕ)(s:ℝ)(m:ℕ)(hs:0<s):∃ c:ℝ,0≤c ∧∀ x:Signed, ∀ A:I→ Atom G n, ∀ U, SumBudget (fun i=>(A i).budget s) U → Earn r m (exactAtoms A x) (paymentAtoms A x r) (c*U):=by
    obtain ⟨C,hc,H⟩:= sphereTurns (I:=I×Cue G n) G (heraldD G) (s/2) (lumenD G) (by positivity) m r n; exact ⟨C,hc,fun x A U hp=> H _ _ _ (smelt_cost hp hs x) fun i j=>brightD _ _ _⟩
-- core loop price and sums.
abbrev gateUnit (G:Gauge)(q:PlaqAxes)(s:Signed)(_:Unit): Chant G 1:= fun _=>plaqBeam G q s
abbrev facePrice (G:Gauge)(q:PlaqAxes)(s: Signed):= rhythm (gateUnit G q s) 1
abbrev cardingF (G:Gauge)(q:PlaqAxes)(s:Signed)(r:ℕ):= timbre (gateUnit G q s) 1 r
lemma priceValue (q:PlaqAxes)(s:Signed)(V:CoverConfig G): facePrice G q s V= G.price (faceValue (pull s 0 V) (0,q)):=by unfold facePrice rhythm; rw [tsum_fintype]; simp only [Fintype.univ_punit,Finset.sum_singleton,Pi.one_apply,one_mul,verseX,Fin.prod_univ_one]; exact plaqBeamEq ..
lemma ledgerF (p:PlaqAxes)(v:Signed)(G: Gauge)(s:ℝ): saturate (gateUnit G p v) 1 s (Real.exp (s*4)):=by
    refine ⟨fun _=>by positivity, (hasSum_fintype _).summable, ?_⟩; rw [tsum_fintype]; simp only [Fintype.univ_punit,sum_singleton,Pi.one_apply,norm_one,one_mul,lawn,Fin.sum_univ_one]; exact le_of_eq (congr_arg (fun v:ℕ=>Real.exp (s*v)) (show (plaqBeam G p v).leg.length=4 by simp [square])) -- coe 4
abbrev twin (R:PathData G)(x:Signed)(p:PlaqAxes)(i:G.ColorIndex)(r:ℕ):= timbre (duetU R p x i) (penny R p) r
abbrev twinV (R:PathData G)(x:Signed)(p:PlaqAxes)(i:G.ColorIndex):= rhythm (duetU R p x i) (penny R p)
abbrev waistX (R:PathData G)(k:Clip)(x:Signed)(p:PlaqAxes)(r:ℕ):= k.direct • cardingF G p x r+(1/2:ℝ) • ∑ i, twin R x p i r
abbrev waistV (R:PathData G)(k:Clip)(x:Signed)(p:PlaqAxes) := k.direct • facePrice G p x+(1/2:ℝ) • ∑ i, twinV R x p i
abbrev loftX (R:PathData G)(k:Clip)(x:Signed)(r:ℕ):= (∑ i, waistX R k x i r) + paymentAtoms R.cubic x r + paymentAtoms R.quartic x r
abbrev loftV (R:PathData G)(k:Clip)(x:Signed):=(∑ i, waistV R k x i) + exactAtoms R.cubic x + exactAtoms R.quartic x
section
variable {R: PathData G}{p:Clip}
lemma repute (G:Gauge)(p:Clip)(s b:ℝ)(hs:0<s)(r m:ℕ):∃ c:ℝ, ∀ R:PathData G,∀ U, R.Bounds p s b U→∀ x: Signed, Earn r m (loftV R p x) (loftX R p x r) c:=by
    obtain ⟨C,hC,H⟩:=sphereTurns (I:=ℕ×ℕ) G _ (s/2) (lumenD G) (by positivity) m r 2; obtain ⟨F,hF,W⟩:=sphereTurns (I:=Unit) G _ _ (lumenD G) hs m r 1; obtain ⟨X,hX,A⟩:= emp ℕ G 3 r s m hs; obtain ⟨Y,hY,Q⟩:= emp ℕ G 4 r s m hs
    refine ⟨_,fun R U h x=>earnSum (earnSum (earnSet univ (waistV R p x) (fun i=> waistX R p x i r)
       (fun _=> ‖p.direct‖*(F*Real.exp (s*4))+‖(1/2:ℝ)‖*(∑ _ :G.ColorIndex,C*(b*b))) (fun i _=> earnSum (earnScale (W _ _ _ (ledgerF i x G s) fun _ _=>litD _ _) _) (earnScale (earnSet univ (twinV R x i) (fun j=>twin R x i j r) _ (fun j _=> H _ _ _ (duet_cost h x i j) (duet_funds R x i j))) (1/2)))) (A x _ b h.three)) (Q x _ b h.four) ⟩ -- fill earn and syntax
end
end Script
end YM.OPE.Flume
