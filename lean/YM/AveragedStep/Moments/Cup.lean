import YM.AveragedStep.Parcel.Plea
/-! A simpler coarse calculus for BP errors. Price any fixed power of
any bounded-card footprint of chords on the joint slice, ALSO with
local gate failure. In the exposed consumers products touching a variable
number of sites need their own preparations (use at fixed arity).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Precision MeasureTheory Function Filter Tree Loops Wilson Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{S:StepData c f}
variable (F:Forest S.ratio)(b:Site c)(τ:ℝ)
def sweepChord (p:TopologyQ F G)(i:Rim c f):ℝ:=τ*G.chord (aboard F b p i)
def cup (D:Finset (Rim c f))(p:TopologyQ F G):ℝ:= 1+∑ i∈D,sweepChord F b τ p i
lemma posChord (h:0≤τ)(p:TopologyQ F G)(i):0≤sweepChord F b τ p i:=mul_nonneg h (G.chord_nonneg _)
lemma cup_ge (h:0≤τ)(D:Finset (Rim c f))(p:TopologyQ F G):1 ≤ cup F b τ D p:=le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>posChord F b τ h p i))
lemma cup_take (h:0≤τ){D:Finset (Rim c f)}{i}(hI:i ∈ D)(p:TopologyQ F G):sweepChord F b τ p i ≤ cup F b τ D p:= by
 unfold cup; exact (Finset.single_le_sum (f:=fun i=>sweepChord F b τ p i) (fun i _=>posChord F b τ h p i) hI).trans (le_add_of_nonneg_left zero_le_one)
lemma chord_env (i:Rim c f):Envelope (fun p:TopologyQ F G=>sweepChord F b τ p i):=env_continuous (continuous_const.mul (G.continuous_chord.comp ((continuous_apply i).comp (aboard_cont F b))))
lemma cup_env (D:Finset (Rim c f)):Envelope (cup F (G:=G) b τ D):=(Envelope.const 1).add (Envelope.sum _ _ (chord_env F b τ))
variable (hS:S.patch.Branches S.kernel G)
include hS
omit hS in
lemma report_scale (d:ℝ)(q:TopologyQ F G→ℝ): report F τ b (d • q)=d*report F τ b q:=by
 -- no hS needed
 unfold report
 simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm (assay F τ b _), integral_const_mul,mul_left_comm _ d]
lemma report_dom {q u:TopologyQ F G→ℝ}(h:Envelope q)(hu:Envelope u)(he:∀ z,|q z|≤u z):
    |report F τ b q| ≤ report F τ b u:=by
 have hz: report F τ b (-q)= -report F τ b q:=by rw [← neg_one_smul ℝ q,report_scale F b τ]; simp
 rw [abs_le]; constructor
 · have hl: report F τ b (-q) ≤ report F τ b u:=by
     rw [← twist_order F b hS (-q) h.neg,← twist_order F b hS _ hu]
     exact read_le S τ hS (fun _=> env_comp h.neg (chamber_meas F b)) (fun _=>env_comp hu (chamber_meas F b)) (fun i z _ => (neg_le_abs (q _)).trans (he _))
   linarith only [hz,hl]
 rw [← twist_order F b hS _ h,← twist_order F b hS _ hu]
 exact read_le S τ hS (fun _=> env_comp h (chamber_meas F b)) (fun _=>env_comp hu (chamber_meas F b)) (fun i z _ => (le_abs_self (q _)).trans (he _))
lemma cup_report (D:Finset (Rim c f))(k:ℕ):
    report F (G:=G) (τ^2) b (fun p=>cup F b τ D p^k) = readQ (G:=G) S (τ^2) (fun i x=> (1+ ∑ z∈D,spokes F τ b z i x)^k) :=by
 rw [← twist_order F b hS _ (env_npow (cup_env F b τ D) k)]
 simp only [cup,sweepChord,spokes,ride]

omit hS F b τ in
lemma cup_price (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(k d:ℕ)(a:ℝ)(ha:0<a):
   ∃ C:ℝ,0≤C∧∀ᶠ τ:ℝ in atTop,∀{c f:Side}(S:StepData c f)(F:Forest S.ratio), Window G S τ P K → ∀ (b:Site c)(D:Finset (Rim c f))(R:ℝ), D.card ≤ d →0≤R→ (∀ i∈D,(separation (S.ratio.embed b) (atRim S i):ℝ) ≤ R) →
   report F (G:=G) (τ^2) b (fun z=>cup F b τ D z^k) ≤ C*lag τ^k*Real.exp (a*R):=by
 by_cases he:k=0
 · subst k; refine ⟨1,zero_le_one,Eventually.of_forall (fun τ c f S F hW b D R _ hr _=> ?_)⟩
   have hS:S.patch.Branches S.kernel G:=by rw [hW.shape,hW.control]; exact h
   rw [cup_report F b τ hS]; simp_rw [pow_zero,read_number S _ hS, one_mul]; exact Real.one_le_exp (by positivity)
 obtain ⟨C,hC,H⟩:=spoke_price G P K h k a ha
 refine ⟨(1+d:ℝ)^k * (1+d*C), by positivity,?_⟩
 filter_upwards [H,eventually_ge_atTop (1:ℝ)] with τ H ht c f S F hW b D R hd hr hD
 have hS:S.patch.Branches S.kernel G:=by rw [hW.shape,hW.control]; exact h
 let q(i:Option (Rim c f)): Query S G:=i.elim (fun _ _=>1) (spokes F τ b)
 let Δ:= Finset.insertNone D
 let B:=C*lag τ^k*Real.exp (a*R)
 let B'(i:Option (Rim c f)):ℝ:=i.elim 1 (fun _=> B)
 have hl:=lag_ge ht
 have h' : Ranked τ (fun i x=>∑ z∈Δ, q z i x) k
    ((Δ.card:ℝ)^k * ∑ i∈Δ,B' i):=by
   apply Ranked.sum hS _ q B' _ he; rintro (_|z) hz
   · change Ranked τ (S:=S) (G:=G) (fun _ _=>1) k 1; simpa only [abs_one,one_pow] using Ranked.const (τ:=τ) (m:=k) hS 1
   simp [Δ,Finset.mem_insertNone] at hz
   exact (H S F hW b z).enlarge (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (hD z hz) ha.le)) (by positivity))
 have hh(i)(x:Board G c f): (∑ z∈Δ, q z i x)= 1+∑ z∈D,spokes F τ b z i x:= by simp [q,Δ,Finset.sum_insertNone]
 rw [cup_report F b τ hS]
 have hp(i:S.Choices)(x:Board G c f): |1 + ∑ z∈D,spokes F τ b z i x|=1+∑ z∈D,spokes F τ b z i x:= abs_of_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun j _=>spoke_pos F (zero_le_one.trans ht) b j i x))
 have hv:=h'.bill; simp_rw [hh,hp] at hv
 apply hv.trans
 simp only [B',Δ,Finset.sum_insertNone,Finset.sum_const,Option.elim,nsmul_eq_mul,Finset.card_insertNone,Nat.cast_add,Nat.cast_one]
 let E:=Real.exp (a*R); have hE:1≤E:=Real.one_le_exp (by positivity); have hL:1≤lag τ^k:=one_le_pow₀ hl
 have hD':(D.card:ℝ) ≤ (d:ℝ):=Nat.cast_le.mpr hd
 change (↑D.card+(1:ℝ))^k*(1 + ↑D.card*B) ≤ _ * _ * E; rw [mul_assoc,mul_assoc]; apply mul_le_mul (pow_le_pow_left₀ (by positivity) (show (↑D.card+(1:ℝ)) ≤ 1+d by linarith) k) _ (by dsimp [B]; positivity) (by positivity)
 unfold B; change 1+D.card*(C*lag τ^k*E) ≤ (1+(d:ℝ)*C)*(lag τ^k*E)
 have hs':0≤ C*(lag τ^k*E):=by positivity
 nlinarith [one_le_mul_of_one_le_of_one_le hL hE, mul_le_mul_of_nonneg_right hD' hs']
end YM.AveragedStep
