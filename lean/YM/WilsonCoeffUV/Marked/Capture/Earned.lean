import YM.WilsonCoeffUV.Marked.Capture.Geometry
/-!
# q-local capture cost aperture at b (age on z only)

Keep exp of polynomial explicitly separate, cannot replace polynomial-
log costs in Prop:kbulk; those produced separately in Mer.

Use center integrated against `HourFace` test and ALL roots, unnormalized
log M retained adjustable (not cancelled on unmatched masks). All coupling
orders. Living bulk earns local envelopes. R.Trace obligations published.
 -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{d:ℕ}{c:Side}{i j i' j' a e r h N n m b b' l:ℕ}{G:Gauge}{σ τ u g B B₀ C x y z ρ β':ℝ}{E W V' U' F':Credit}

section Close
variable {H:Hol G}{Q:Fin (a+1)→ SealR G}{P:Herit Q}{R:Realm G (e+1) E}{X: Wilt Q}{F:Fin (a+1)→ ℝ}
-- exp polynomial-log descriptor, A height log `v=snow b→m` (≥log length `λ_b`) bounded by Z or any Z-poly by padding).
lemma accent {ι:Type}[Fintype ι](k:ι→ℕ)(B:ℝ)(g:0≤B)(m n:ℕ) (A:Credit)(c:ℝ)(_u:0≤c): ∃ W:Credit,∀ z v:ℝ, 1≤ z→0≤v→v≤z→∀ X:ι→ℝ,(∀ i,0≤ X i) →
    (∏ i:ι,B*exp v ^4*(X i*exp v^k i)) * (c*(exp (A.buy z)*exp (m:ℝ))^n)≤ exp (W.buy z) * (∏ i,X i):=by
    let D:ℝ:=∏ _ :ι, B; let K:=4*Fintype.card ι + ∑ i,k i; let T:Credit:= Credit.leanC.prodC (pur (K:ℝ)); let V:= (pur (n:ℝ)).prodC (A.plus (pur (m:ℝ))); let W:Credit:= (T.plus V).plus (pur (D*c));
    refine ⟨W,fun z v hz hv ht X hp=>?_ ⟩; let E:ℝ:= v * K; let U:=(A.buy z+m)*n; let L:=∏ i,X i; have hD:0≤D:=Finset.prod_nonneg fun _ _=>g; have hL:0≤L:=Finset.prod_nonneg fun i _=>hp i
    have he : E+U+D*c≤ W.buy z:=by
       apply (add_le_add _ (pure_goal ..)).trans (Credit.fuel (T.plus V) (pur (D*c)) hz)
       refine (add_le_add (show E≤T.buy z from ?_) (show U ≤ V.buy z from ?_)).trans (Credit.fuel T V hz)
       · unfold T; rw [Credit.products,Credit.lean_cost]; exact mul_le_mul ht (pure_goal ..) (by positivity) (by positivity)
       unfold V U; rw [Credit.products,mul_comm ((pur (n:ℝ)).buy z)]; apply mul_le_mul (le_trans (b:=A.buy z+(pur (m:ℝ)).buy z) (add_le_add_right (pure_goal ..) _) (Credit.fuel _ _ hz)) (pure_goal ..) (by positivity) (zero_le_one.trans (Credit.purchase _ hz))
    have hq : (∏ i:ι, B*exp v ^4*(X i* exp v ^k i))=D*L*exp E:=by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ, Finset.prod_pow_eq_pow_sum]
        unfold D L E; rw [mul_comm v, Real.exp_nat_mul]; unfold K; rw [pow_add, pow_mul]; rw [Finset.prod_const,Finset.card_univ]; ring
    rw [hq,← Real.exp_add,← Real.exp_nat_mul,mul_comm (n:ℝ),show D*L*exp E * (c*exp U)=(D*c * exp (E+U))*L by rw [exp_add]; ring]
    refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (show D*c≤ exp (D*c) from by linarith only [Real.add_one_le_exp (D*c)]) (by positivity : 0≤ exp (E+U))).trans ?_) hL; rw [← Real.exp_add,add_comm]; exact Real.exp_le_exp.mpr he
-- qCTA quantitative kme supply. Center integral across positions of full joint and poly Strict op telescope.
structure Shipfit (S: Schedule)(Q:Fin (a+1)→SealR G)(X:Wilt Q)(m b:ℕ)(ρ z:ℝ)(F:Fin (a+1)→ℝ) (B:ℕ): Prop where
    roadm : b≤m
    hail : snowP S b m≤ z
    amp i:Amplitude (X i) (F i)
    within_r i: (X i).radius ≤ B*paceT S m b
    lens i j:i≠j→ClearDay (X i) (X j) (ρ+14)
lemma invoke (H:Hol G)(Q:Fin (a+1)→SealR G)(e:ℕ)(E W V' U' F':Credit)(B:ℕ): ∃ X':Credit,∀ (R:Realm G (e+1) E)(_P:Tribe R H W V' Q)(m b N)(_u:b≤m)(_v:m≤ N)(h:R.anchor≤ b)(X:Wilt Q)(A:Fin (a+1)→ℝ)(V:Herit Q)(ρ z:ℝ)(D:ℕ),
    let C:= (dictated H Q E W V' U' e).choose
    let k:= asp Q; let d:= (fun i=>(Q i).D); Cloze d k R F'→ PadRank R b m z → galeGate G d k k e C F' E z ≤ρ →Shipfit R.draws.S Q X m b ρ z A B → (∀ i,sprouted (Q i) (V i) e (U'.buy z)) →∀ i≤e, ∀ r, Cork Bank.terrain 0 (Vσ R b h) (Real.exp (X'.buy z)*(∏ i,A i)) ((AutumnDay R.draws R.paid X V m b N D).2 i r):=by
    let C:= (dictated H Q E W V' U' e).choose; let k:=asp Q; let d (i):=(Q i).D; let U:=wintry G d k k e C F' E Credit.unit; let Z:=lengthC G d k e; let Y:ℕ:= (2*yardLen B+1)^4
    obtain ⟨V,q⟩:=accent d (Y:ℝ) (by positivity) (4*yardLen B) (Fintype.card (Fin (a+1))) U Z (formalO G d k Finset.univ e).choose_spec.1
    refine ⟨V,?_ ⟩; intro R P m b N u v h X A L ρ z D C k' D' H' w t x hp i f r
    let T:= coatA R.draws R.paid N m Q L; have ht:= (dictated H Q E W V' U' e).choose_spec R P m N L z (h.trans u) v (w.year _ u le_rfl) hp
    have hz:1≤z:=le_trans (R.depth _ h) (w.year _ le_rfl u); let s:=R.draws.S; let F:=outset R m N ρ k k T; let K:= Gears R.draws R.paid k k N m b F
    have hX: Wellness k F:=reserveSpec _ _ _ _ (Cog _ _ le_rfl T (cloister P L (h.trans u) v) R.hG R.green v)
    let z':= snowP s b m; have hy:0≤z':= sub_nonneg.mpr (scales s u); let θ:= paceT s m b; have hθ: θ= exp z':=by unfold θ z' snowP; rw [pace_rep, neg_sub]
    have hz': Uniform R K b h (exp (U.buy z)):= nearExponential H' F hX h u v (fun p S=> earn_cap ht H' t v p S) w (show C.buy z ≤ exp (C.buy z) by linarith only [Real.add_one_le_exp (C.buy z)]) (zero_le_one.trans (C.purchase hz))
    let E:= exp (V.buy z)*(∏ i,A i); let W:= LodeStar R.draws R.paid X L m b N θ
    have hf o: Cork Bank.terrain 0 (Vσ R b h) E ((locale o W).2 i r):=by
        rw [show locale o W=_ from (close_eq R H Q P (h.trans u) v L X o θ u x.lens).symm]
        apply (pedal (pace_ge _ u) (exp_pos (U.buy z)).le K X (Cog _ _ v _ hX R.hG R.green u) A x.amp x.within_r h hz' f o).cost
        have he:= q z z' hz hy x.hail A (fun i=> (x.amp i).1); rw [← hθ] at he; exact he
    refine ⟨(hf zeroC).1,fun p=> ((hour_price dayMeasure (W.2 i r p) D).trans (le_trans (integral_mono (readyCash dayMeasure (W.2 i r p) |>.norm) (integrable_const _) (fun w=>(hf w).2 p)) ?_))⟩
    simp only [integral_const,probReal_univ, one_smul]; exact le_rfl
end Close
end YM.WilsonCoeffUV.Wheel.Flooring
