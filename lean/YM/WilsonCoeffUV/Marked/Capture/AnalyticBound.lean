import YM.WilsonCoeffUV.Marked.Capture.JointMeasures
/-!
# Full joint prices analytic: keep a specified origin, root sums restored

Uses moment power times true-width exponential, finite tensor order. The hull
requirement in realization can ask extra polynomial/geometric beforehand.
`Postal` includes derivative carriers only in a label's own unit cell; for
continuum thin connectors budgeting their lengths one may also spend `2*S`.
Resolution in lattice link counts; no period winding estimate except lifted.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Address
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{o:ι}{J I S T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}
variable [DecidableEq ι]
-- Root assignment held (o,p(o)). Outside lazy can use any.
def toe (S:Finset ι)(O:ι)(p:Cover)(Q:(S.erase O)→ Cover)(v:ι): Cover:= if v=O then p else if h:v∈ S.erase O then Q ⟨v,h⟩ else p
lemma toeO (S:Finset ι)(o:ι)(p:Cover)(Q:S.erase o→Cover): toe S o p Q o=p:= if_pos rfl
abbrev Fence (α:Type)(S:Finset ι)(o:ι)(i:ℕ):= (↑(S.erase o) → Cover) × dock Cover α i
def lineOut (p:ι→Cover)(S:Finset ι)(o:ι)(x:dock Cover α r):ℝ:= 1+2*S.card + ∑ i∈S,(Bank.terrain.gap (p o) (p i):ℝ) + ∑ i,(Bank.terrain.gap (p o) (x i).1:ℝ)
omit [DecidableEq ι] in
lemma lineBound {α:Type}{p:ι→Cover}(q:o∈S)(x:dock Cover α r) : 1≤lineOut p S o x ∧ lineOut p S o x ≤ (1+2*S.card+r:ℝ)*(1+(Syn Bank.terrain p S x:ℝ)):=by
    unfold lineOut; let V:=foyer p S x; let i:↥S:=⟨o,q⟩; set X:ℝ:= ↑(Syn Bank.terrain p S x); have hx:0≤X:=by unfold X; positivity
    have hp:= Finset.sum_le_sum (fun j (h:j∈S)=> (show (Bank.terrain.gap (p o) (p j):ℝ)≤ X from Nat.cast_le.mpr (leg_le Bank.terrain V (.inl i) (.inl ⟨j,h⟩))))
    have hq:= Finset.sum_le_sum (fun j (_:j∈Finset.univ)=> show (Bank.terrain.gap (p o) (x j).1:ℝ)≤ X from Nat.cast_le.mpr (leg_le _ V (.inl i) (.inr j)))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hp hq; constructor
    · have f:=Finset.sum_nonneg (s:=Finset.univ) (fun i _=>show 0≤(Bank.terrain.gap (p o) (x i).1:ℝ) by positivity); have h:=Finset.sum_nonneg (s:=S) (fun i _=>show 0≤(Bank.terrain.gap (p o) (p i):ℝ) by positivity); linarith
    nlinarith only [hx,hp,hq, show (0:ℝ) ≤ r by positivity, show 0≤ S.card * X by positivity]

-- one origin fixed all possible addresses of the others. payment even includes
-- dummy unused mark tuple entries in an address table (there is NO sum over
-- root positions not belonging to this slot set).
def towerV {α U:Type}(S:Finset ι)(o:ι)(j:ℕ)(P : (ι→ Cover) → Ten U (Cloth α) j)(x:Cover)(p:Fence α S o j):= P (toe S o x p.1) p.2
def PostMark (S:Finset ι)(o:ι)(j:ℕ)(P:(ι→Cover)→ Ten (Pen D S) (Cloth α) j)(σ B:ℝ)(r:ℕ):Prop:=∀ x,∃ μ:Fence α S o j→Measure (Post D),(∀ i,(μ i).Regular ∧ IsFiniteMeasure (μ i))∧(∀ i (v:Tent D), touch (fun i=> page _ (v i)) S (towerV S o j P x i)=∫ y,pts S v y ∂(μ i)) ∧ SumBudget (fun i:Fence α S o j=> lineOut (toe S o x i.1) S o i.2^r *Real.exp (σ*Syn Bank.terrain (toe S o x i.1) S i.2)*(μ i).real univ) B
lemma sprigS [Fintype α] {p:Cover}(x:0<σ)(i:ℕ): SumBudget (fun y:dock Cover α i=> sail (σ/i) Bank.terrain p y) (tiePay α i σ):=by
    cases i with | zero=>simp [sail,SumBudget,tiePay]; exact summable_of_hasFiniteSupport (Set.toFinite _) | succ i=> exact train_pay (div_pos x (by positivity)) p _
abbrev Exped (G:Type)[Fintype G] (i:ℕ)(B:ℝ):ℝ:= offerQ G i 0 B
lemma snuff [Fintype α] (h: 0<σ)(p:σ⁻¹≤B):tiePay α r (σ/8) ≤ Exped α r (2*B):=by
    have he: (σ/2)⁻¹ ≤ 2*B := by rw [inv_div]; calc (2:ℝ)/σ=2*σ⁻¹:= div_eq_mul_inv ..
                                                    _ ≤ _:=mul_le_mul_of_nonneg_left p (by norm_num)
    have hx:= tideQ (α:=α) (k:=r) (div_pos h (by norm_num) :0<σ/2) he; unfold Exped offerQ; simp only [pow_zero,one_mul]; rw [show σ/8=σ/2/4 by ring]; exact hx

lemma sandCW (q:o∈S)(C:Cover)(i:Fence α S o r)(p:0<σ):
   let Z:= Syn Bank.terrain (toe S o C i.1) S i.2; let V:= σ/8
   let K:=Fintype.equivFin (↑(S.erase o)); let L:Fin (Fintype.card (↑(S.erase o)))→ Cloth Unit:=fun x=> (i.1 (K.symm x),())
   exp (-(σ/4)*Z) ≤ sail (V/Fintype.card (↑(S.erase o))) Bank.terrain C L * sail (V/r) Bank.terrain C i.2:=by
    intro Z V K L; let P:=toe S o C i.1; let α:= ↑(S.erase o); let f:=foyer P S i.2; have hx:0<V:=by unfold V; positivity
    have h0:C=f (.inl ⟨o,q⟩):= (toeO ..).symm
    have he {α:Type}(x:ℕ)(v:dock Cover α x)(s:∀ i:Fin x,Bank.terrain.gap C (v i).1≤ Z): exp (-V*Z)≤sail (V/x) Bank.terrain C v:=by
         cases x with
         | zero=> simp only [sail,Finset.univ_eq_empty,Finset.prod_empty]; exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
         | succ x=> simpa only [sub_zero,neg_zero,zero_mul,exp_zero,one_mul] using sail_cut (d:=Bank.terrain) (Nat.zero_le Z) le_rfl hx (by omega:0<x+1) C v s
    rw [show -(σ/4)*Z = -V*Z+-V*Z by unfold V; ring, Real.exp_add]; refine mul_le_mul (he _ L fun j=>?_ ) (he _ i.2 fun j=>?_ ) (by positivity) (sail_nn ..)
    · let y:= K.symm j; let w:= Finset.mem_erase.mp y.property; let v:= (⟨y.val,w.2⟩:↥S); have ht:f (.inl v)= (L j).1:=by change toe S o C i.1 y.val=_; unfold toe; rw [if_neg w.1,dif_pos y.property]
      exact (show Bank.terrain.gap C (L j).1≤ Z from (by rw [h0,←ht]; exact leg_le Bank.terrain f (.inl ⟨o,q⟩) (.inl v)))
    exact Eq.trans_le (congr_arg (fun y=>Bank.terrain.gap y _) h0) (leg_le Bank.terrain f (.inl ⟨o,q⟩) (.inr j))
end YM.WilsonCoeffUV.Wheel.Address
