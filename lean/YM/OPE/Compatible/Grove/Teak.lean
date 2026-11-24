import YM.OPE.Compatible.Glow.Greet
/-! Real bundles from actual Path terms. Triple packs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
-- pack atoms on pull signed stencil
abbrev Cue (G:Gauge)(k:ℕ):=Fin k→G.ColorIndex
def smelt (P:I→ Atom G n)(s: Signed)(x: I × Cue G n):Chant G n:=fun i=>slotBeam ((P x.1).leg i) s (x.2 i)
def brass (P:I→ Atom G n)(x:I ×Cue G n):= (P x.1).coeff x.2
lemma rangeS (a: RG.Slot)(s:Signed)(x:G.ColorIndex): (slotBeam a s x).leg.length= 2*a.walk.length +4:=by simp [square,Lattice.reverse]; omega
lemma smeltL (P:I→ Atom G n)(s:Signed)(x): lawn (smelt P s x) ≤ 2*(P x.1).length:=by
    unfold lawn Atom.length smelt; rw [mul_sum]; exact sum_le_sum (fun i _=>by rw [rangeS]; unfold RG.Slot.length;omega)
lemma smelt_cost {P:I→ Atom G n}(h:SumBudget (fun i=> (P i).budget s) b)(hs:0<s)(x: Signed):saturate (smelt P x) (brass P) (s/2) b:=by
    let c(i:I)(p:Cue G n):= ‖(P i).coeff p‖ * Real.exp (s*(P i).length); have ht (i:I): SumBudget (c i) ((P i).budget s) := ⟨fun p=> mul_nonneg (norm_nonneg _) (Real.exp_pos _).le, (hasSum_fintype _).summable, by unfold Atom.budget Atom.magnitude; rw [Finset.sum_mul,tsum_fintype];rfl⟩ -- le_rfl
    let f: I×Cue G n→ℝ:=uncurry c; have he:Summable f:= (summable_prod_of_nonneg (f:=f) fun i=> (ht i.1).1 i.2).mpr ⟨fun i=>(ht i).2.1,h.2.1.of_nonneg_of_le (fun i=>tsum_nonneg (ht i|>.1)) (fun i=>(ht i).2.2)⟩
    let M(i:I):=(P i).budget s; have hh:SumBudget f b:=⟨fun i=>(ht i.1).1 i.2,he, he.tsum_prod.trans_le ((he.prod.tsum_le_tsum (fun i=> show (∑' j,c i j)≤M i from (ht i).2.2) h.2.1).trans h.2.2)⟩
    unfold saturate; apply budget_minor hh (fun _=>by positivity); intro p; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (norm_nonneg _) -- hp rearrange
    have hz:= (Nat.cast_le (α:=ℝ)).mpr (smeltL P x p); rw [Nat.cast_mul,Nat.cast_ofNat] at hz; linarith only [mul_le_mul_of_nonneg_left hz hs.le]
lemma pleatFit (G:Gauge) :∃ d:ℝ,0≤ d ∧ ∀ i:G.ColorIndex,∀ t:G.Mat, ‖pleatsF i t‖ ≤ d*‖t‖:=by
    choose v hv h using fun i:G.ColorIndex=> ContinuousLinearMap.bound (F:=ℝ) (E:=G.Mat) (𝕜:=ℝ) (𝕜₂:=ℝ) (σ₁₂:=RingHom.id ℝ) ((pleatsF i).toContinuousLinearMap)
    exact ⟨∑ i,v i,sum_nonneg fun i _=>(hv i).le,fun i t=>(h i t).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun j _=>(hv j).le) (mem_univ i)) (norm_nonneg _))⟩
lemma traceFit (G:Gauge):∃ d:ℝ,0 ≤ d ∧ ∀ t:G.Mat, ‖traceF G t‖ ≤ d*‖t‖:=by obtain ⟨v,h,hx⟩:= ContinuousLinearMap.bound (F:=ℝ) (E:=G.Mat) (𝕜:=ℝ) (𝕜₂:=ℝ) (σ₁₂:=RingHom.id ℝ) ((traceF G).toContinuousLinearMap); exact ⟨_,h.le,hx⟩
abbrev heraldD (G:Gauge):= max (pleatFit G).choose (traceFit G).choose
lemma lumenD (G:Gauge):0≤ heraldD G:=(traceFit G).choose_spec.1.trans (le_max_right ..)
lemma brightD (x:RG.Slot)(j:Signed)(i:G.ColorIndex)(y:G.Mat):‖(slotBeam x j i).f y‖ ≤ heraldD G * ‖y‖:= ((pleatFit G).choose_spec.2 i y).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
lemma litD (p:PlaqAxes)(v:Signed)(y:G.Mat): ‖(plaqBeam G p v).f y‖ ≤ heraldD G * ‖y‖:= ((traceFit G).choose_spec.2 y).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
lemma prod_group (p:Chant G n)(V:CoverConfig G)(h:0 ≤ s)(hg:moderateX p s): ‖verseX p V‖≤(s*(2*G.colorScale))^n:= by
    have he(i:G.El): ‖G.mat i‖=G.colorScale:= Gauge.unitary_frob (G.mat_mul_star _); unfold verseX; rw [norm_prod,← show (∏ _ : Fin n,s*(2*G.colorScale))=(s*(2*G.colorScale))^n from by rw [prod_const, card_univ,Fintype.card_fin]]; apply prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> ?_; apply (hg i _).trans; apply mul_le_mul_of_nonneg_left _ h; apply (norm_sub_le ..).trans; rw [← G.mat_one, he, he]; ring_nf; rfl
lemma rhythm_sum (p:I→ Chant G n)(x:I→ℝ)(g:saturate p x s U)(hs:0 ≤ s)(hd:0≤D)(hg:∀ i,moderateX (p i) D)(v:CoverConfig G): Summable fun i=> x i*verseX (p i) v:=by
    apply (g.2.1.mul_right ((D*(2*G.colorScale))^n)).of_norm_bounded fun i=>?_ ; rw [norm_mul]; exact mul_le_mul (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))) (prod_group (p i) v hd (hg i)) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by positivity))
lemma gears(A:I→ Atom G n)(s:Signed)(v:CoverConfig G) (hs:0<b)(h:SumBudget (fun i=>(A i).budget b) U):
    rhythm (smelt A s) (brass A) v= ∑' i,(A i).poly (fun j=>((A i).leg j).eval (pull s 0 v)):=by
       unfold rhythm; rw [(rhythm_sum _ _ (smelt_cost h hs s) (by positivity) (lumenD G) (fun i j=> brightD _ _ _) v).tsum_prod]; refine tsum_congr fun i=>?_ ; unfold Atom.poly; rw [tsum_fintype]; apply sum_congr rfl; intro j _; apply congr_arg ((A i).coeff j *·); exact prod_congr rfl fun k _=>slotBeamEq ..
end Script
end YM.OPE.Flume
