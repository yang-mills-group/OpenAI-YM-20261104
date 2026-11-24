import YM.RegulatorIR.Older.Trunk
import YM.RegulatorIR.Clocks.Test

/-!
# Coefficientwise trunk equivalence past requested precision

Top/primal couplings and symbol T rotations need not agree in higher jets.
Input BIOS kept fixed under independent periodic choices. Supports at overlap before
limits. Explicit arithmetic not coercing truncated reals as Taylor dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Clocks
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Older Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {p r n s d m i j:ℕ}{G:Gauge}{W I Y Z V:Type}{c f c' f': Side}
lemma movesV {A X Y: Writing}(hv: Squares p X Y)(h:∀ i,i<d→coeff i A=0): Squares (p+d) (X*A) (Y*A):=by
 intro i hi;rw [coeff_mul,coeff_mul];apply sum_congr rfl;intro j hj;have hh:=mem_antidiagonal.mp hj; by_cases ht:j.2<d
 · rw [h _ ht];simp
 rw [hv _ (by omega)]
lemma inv_v {A B: Writing}(h:Squares p A B)(ht: coeff 0 A≠0)(hh: coeff 0 B≠0): Squares p A⁻¹ B⁻¹ := by
 apply Squares.left ht; have he:=h.maintains (show Squares p B⁻¹ B⁻¹ from fun _ _=>rfl); rw [PowerSeries.mul_inv_cancel B _] at he; rw [PowerSeries.mul_inv_cancel A _];exact fun i hi=>(he i hi).symm
 all_goals rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
lemma grows_sq {f:ℝ→ℝ}(_h: ContDiffAt ℝ ∞ f 0)(hi: ∀ x,f x≥0)(hv:f 0=0):∀ i:ℕ,i<2→ coeff i (tale f)=0:=by
 intro i he; have hp:i=0 ∨ i=1:=by omega
 rcases hp with hp|hp
 · subst i; rw [tale_base,hv]
 subst i
 have hm : IsLocalMin f 0:= eventually_of_mem univ_mem fun i _=> show f 0≤ f i from hv.symm ▸ hi i
 rw [tale,inscription, coeff_mk, jet]; rw [show iteratedFDeriv ℝ 1 f 0 (fun _=>1)=fderiv ℝ f 0 1 from iteratedFDeriv_one_apply .., hm.fderiv_eq_zero]; simp

-- using scale β clock jets. $Coeff i+a$ branches equal so polar uniqueness.
variable (P Q:Binding.Scale)(v: Squares p (tale P.beta) (tale Q.beta))
include v
lemma plain_agree (x:Foot G→ℝ)(a:Face ℤ):Squares (p+2) (tale (flank (plain P G a) x)) (tale (flank (plain Q G a) x)):=by
 let f:=flank (plain flat G a) x
 have hf:ContDiffAt ℝ ∞ f 0:= (boons G flat a).some.smooth_v _
 have he(t):0≤ f t:= by unfold f flank plain; exact mul_nonneg (flat.forward _) (G.price_range _).1
 have hx:f 0=0:=by unfold f flank; rw [zero_smul]; exact plain_rest ..
 have hg (P : Binding.Scale) : tale (flank (plain P G a) x)= tale P.beta*tale f:=by rw [show flank (plain P G a) x=P.beta*f from ?_,tale_mul P.near hf]; ext1 i;change _= P.beta i*(1*_);rw [one_mul];rfl
 rw [hg P,hg Q]; exact movesV v (grows_sq hf he hx)
lemma prism_agree (T:StepData c f)(N:T.patch.Branches T.kernel G) (x:KFoot G→ℝ)(i:Branchix):
 Squares (p+barkN i) (tale (flank (prism T (bios T) P i) x)) (tale (flank (prism T (bios T) Q i) x)):=by
 cases i
 next i=> exact fun _ _=>rfl
 next i=>
   let f:=flank (opi T flat i) x; have hf:ContDiffAt ℝ ∞ f 0:= (locally T N flat i).some.smooth_v _
   have he:f 0=0:=by unfold f flank; rw [zero_smul]; exact opi_zero T N flat i 0
   have ht (v):0≤ f v:=by unfold f flank opi; apply mul_nonneg (mul_nonneg (flat.forward _) (T.kernel.penalty_pos.le)) (G.price_range _).1
   have hp (P: Binding.Scale) : tale (flank (prism T (bios T) P (Sum.inr i)) x)=tale P.beta*tale f:=by rw [← tale_mul P.near hf];apply congr_arg;ext t;change P.beta t*T.kernel.penalty*_=P.beta t*(1*T.kernel.penalty*_);ring
   rw [hp,hp]; exact movesV v (grows_sq hf ht he)

omit v

-- graded coefficient recognition on Θ. equality through p sufficient across heights.
def Matches {I:Type}(e:ℕ)(T W: Orders I):Prop:= ∀ i,i≤e→T i=W i
lemma stageM {F G:Micro I}{T W:Orders I}{c:ℝ} (h: Lab n c F T)(hx:Lab n c G W)(ht:∀ x,Squares (p+n) (tale (flank F x)) (tale (flank G x))): Matches p T W:=by
 intro i hi; cases Nat.eq_zero_or_pos i with
 | inl hh=> subst i; exact h.awake.trans hx.awake.symm
 | inr hg=> exact guessed (h.scope_ i) (hx.scope_ i) (h.smooth i) (hx.smooth i) fun v=>by rw [h.figures v hg,hx.figures v hg,ht v _ (by omega)]
lemma prism_now (T:StepData c f)(S':StepData c' f')(L: Scale)(Y: Scale){Z Z':Branchix→ Orders (KFoot G)}(he: T.patch=S'.patch)(hp:T.kernel=S'.kernel)(N:T.patch.Branches T.kernel G)(h:Sphere T (bios T) L Z)(hv:Sphere S' (bios S') Y Z')(ht : Squares p (tale L.beta) (tale Y.beta)):∀ j,Matches p (Z j) (Z' j):=by
 intro j; apply stageM (h j) (hv j);intro v; rw [← neverP T S' he hp Y]; exact prism_agree L Y ht T N v j

section Heat
variable {P Q:ℝ}{L:Layer I I}{U G F F':Type}{A:Deck P I Z}{B:Deck P Y U}{C:Deck Q I F}{D:Deck Q Y F'}
lemma heat_m (f: Bool){T W: Orders I}(h: Matches p T W):∀ k,Matches p (logHeat L T f k) (logHeat L W f k):=by
 intro k; induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i hi;ext1 r; cases k
    · rw [logHeat_first,logHeat_first,h i hi]
    next k=> rw [logHeat_next,logHeat_next, ih k (by omega) i hi]; split;rfl; apply congr_arg; apply congr_arg;apply congr_arg; unfold Diagram.drift; apply sum_congr rfl; intro j hj; unfold Diagram.carry; apply sum_congr rfl; intro p hp;have hh:= mem_antidiagonal.mp hj;have hv:= mem_antidiagonal.mp hp;rw [ih j.1 (by omega) p.1 (by omega), ih j.2 (by omega) p.2 (by omega)]
lemma mark_m {V G:Orders I} {T S:ℕ→Orders I}(h:Matches p V G)(hp:∀ i, Matches p (T i) (S i)):∀ k, Matches p (markHeat L T V k) (markHeat L S G k):=by
 intro k; induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i hi; ext1 v; cases k
    · rw [markHeat_first,markHeat_first,h i hi]
    next k=> rw [markHeat_next,markHeat_next, ih k (by omega) i hi];apply congr_arg;apply congr_arg;unfold Diagram.drift;apply sum_congr rfl;intro j hj;unfold Diagram.carry;apply sum_congr rfl;intro q hq;have hh:=mem_antidiagonal.mp hj;have hv:= mem_antidiagonal.mp hq;rw [ih _ (by omega) q.1 (by omega), hp _ _ (by omega)]
structure GridM (P:GridStep A B)(Q:GridStep C D)(p:ℕ): Prop where
 stm:P.line=Q.line
 dgn:P.driftL=Q.driftL
 gear: Matches p P.addon Q.addon
variable {P':GridStep A B}{Q':GridStep C D}
namespace GridM
variable (HS:GridM P' Q' p)
include HS
lemma joint_m {T U: Orders I}(h:Matches p T U): Matches p (P'.jVac T) (Q'.jVac U):= by
 intro i hi; ext1 r; unfold GridStep.jVac; rw [h i hi, HS.gear i hi];rfl
omit HS in
lemma offers_v {T U:Orders I}(h:Matches p T U): Matches p (fun i r=>offer (firstChannel A B).native (T i r)) (fun i r=> offer (firstChannel C D).native (U i r)):=by intro i hi;dsimp only; rw [h i hi];rfl
lemma log_step {T W:Orders I}(h:Matches p T W):Matches p (P'.pure T) (Q'.pure W):=by
 intro i hi; ext1 r; unfold GridStep.pure; rw [HS.stm];split;rfl
 unfold GridStep.pullI; rw [HS.dgn]; apply congr_arg (crop (lastChannel C D).native);apply congr_arg; unfold ceaseHeat heated;apply sum_congr rfl; intro j _; rw [heat_m false (HS.joint_m h) j i hi]
lemma wave_step {T V A Y:Orders I} (h:Matches p T V)(hp:Matches p A Y): Matches p (P'.each m T A) (Q'.each m V Y):=by
 intro i hi; ext1 r; unfold GridStep.each GridStep.pullI;rw [HS.stm,HS.dgn]; apply congr_arg (crop (lastChannel C D).native);apply congr_arg;unfold endHeat heated; apply sum_congr rfl;intro j _
 exact congr_fun (mark_m (offers_v hp) (heat_m false (HS.joint_m h)) j i hi) r
end GridM
end Heat
end YM.RegulatorIR.Clocks
