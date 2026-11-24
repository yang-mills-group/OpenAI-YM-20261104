import YM.Comparison.RG02.Adjacent.Shadow
/-!
# Sale via the rank-priced basis

Change of external real aperture variables/primitives after computing the Fk orders. This is
coordinate and coupling re-expression of the *series on REAL groups*: ranked directions & tangent
tensors on unconstrained Log side. Uses only the available orders before the next reset. Carries
`expense` Z including possible MARK d so evaluates e.g. a threshold marker instruction to scale by
`rating t` itself first. Need orientation-specific costs outside. Rates only fixed per scheme germ
until supplied (`UnitCost`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

local notation "φ"=> 𝓝 (0:ℝ)
local notation "λ₀"=> (ω:WithTop ℕ∞)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma levelJet {f:X→Y} (h : ContDiffAt ℝ ω f 0)(i:ℕ): Level i (Assembly.jet f i):= by
   induction i generalizing f with
   | zero=> rw [funext (Assembly.jet_zero f),Nat.cast_zero]; exact Level.constant _
   | succ k ih=>
     let Z:= Assembly.jet f (k+1); have hu: ContDiff ℝ ω Z:= Tensor.diag_smooth (Tensor.coeff f (k+1) 0) _
     apply Level.up (by positivity) hu; intro v
     have ht : Analysis.D v Z=Assembly.jet (Analysis.D v f) k:= funext fun x=> Tensor.slot_lower (h.of_le le_top) v x
     change Level _ (Analysis.D v Z)
     rw [ht, show ((k+1:ℕ):ℤ)-1= k by omega]; exact ih (Analysis.dSmooth h v (by simp))

abbrev Display (X:Type*) := ℕ→X→ℂ
variable (U : Display X) (K : UnitCost) (d : ℤ) (r : ℕ)

def tags (d:ℤ)(i k : ℕ)(u:ℝ):ℝ:=u^d*(u^i*(u⁻¹)^k)
-- allow Z Laurent leading weight d.
def money (i k:ℕ)(t:ℝ) : ℂ:= t^i * (tags d i k (K.rating t):ℂ)
lemma exchange (i k : ℕ) {x : ℝ} (h : x≠0): tags d i k x=x^(d+i-k) := by simp only [tags,zpow_sub₀ h,zpow_add₀ h, zpow_natCast, div_eq_mul_inv, inv_pow]; ring
lemma checks (i k:ℕ): ContDiffAt ℝ ω (fun t=> tags d i k (K.rating t)) 0:= (K.spin d).mul ((K.smooth.pow i).mul ((K.spin (-1)).congr_of_eventuallyEq (Eventually.of_forall (fun _=> (zpow_neg_one _).symm))|>.pow k))
lemma monetized (i k:ℕ) : ContDiffAt ℝ ω (money K d i k) 0:= (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (checks K d i k))

-- evaluated with ACTUAL reparameterizer u, never identifying from the prescribed curve
-- unless actual charge was matching. Neg exponents (u) require Unit assumption for physical use.
def cover (r:ℕ) (t : ℝ)(x:X): ℂ:= ∑ i∈range (r+1), (t:ℂ)^i*U i x
def ages (t : ℝ)(u:ℝ) (x:X):= (↑(u^d : ℝ):ℂ) * cover U r (t*u) (u⁻¹ • x)
def born (r:ℕ) (i:ℕ) (x:X) := motion (fun t=> ages U d r t (K.rating t) x) i

variable {U}
abbrev Charge (r:ℕ)(p:ℕ→ℤ)(f:Display X) := ∀i≤r, Level (p i) (f i)
variable {m:ℕ→ℤ} (hp : Charge r m U)
include hp
private lemma paid (i:ℕ) (h:i≤r): Level (↑((m i).toNat)) (U i) := (hp i h).promote (Int.self_le_toNat _)
lemma quoted (t u:ℝ) (x:X): ages U d r t u x=∑ i∈range (r+1), ∑ k∈ range ((m i).toNat+1), ((t:ℂ)^i * (tags d i k u:ℂ))*Assembly.jet (U i) k x := by
    unfold ages cover; rw [mul_sum]; apply sum_congr rfl; intro i hi
    have hx:= (paid r hp i (mem_range_succ_iff.mp hi)).posted (u⁻¹ • x)
    rw [hx,mul_sum,mul_sum]; simp_rw [Clipper.weight]; apply sum_congr rfl; intro k hk; unfold tags; rw [Complex.real_smul]; push_cast; ring
lemma message (i:ℕ) (x:X) : born U K d r i x=∑ j∈range (r+1), ∑ n∈ range ((m j).toNat+1), motion (money K d j n) i * Assembly.jet (U j) n x := by
    unfold born; simp_rw [quoted d r hp]
    let f j n (t:ℝ):= money K d j n t * Assembly.jet (U j) n x; have hf (j n:ℕ) : ContDiffAt ℝ ω (f j n) 0:= (monetized K d j n).mul contDiffAt_const
    change motion (fun t=> ∑ j∈ range (r+1), ∑ n∈ range ((m j).toNat+1), f j n t) i=_
    rw [msum (f:=fun j t=> ∑ n∈ range ((m j).toNat+1), f j n t) _ fun j _=> ContDiffAt.sum fun n _=> hf j n]; apply sum_congr rfl; intro j _
    rw [msum _ _ fun n _=> hf j n]; unfold f; apply sum_congr rfl; intro n _; rw [show (fun x'=>money K d j n x' * Assembly.jet (U j) n x) = _ from funext (fun x'=> mul_comm (money K d j n x') (Assembly.jet (U j) n x)),mul_comm _ (Assembly.jet (U j) n x)]; exact mscale _ (monetized K d j n)
omit hp
lemma triangular (i j k:ℕ) : motion (money K d j k) i= if j≤ i then motion (fun t=> (tags d j k (K.rating t):ℂ)) (i-j) else 0 := mono_price (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (checks K d j k))
lemma this_step (i k:ℕ): motion (money K d i k) i=1 := by rw [triangular,if_pos le_rfl,Nat.sub_self,mzero]; simp [tags,K.origin]
include hp
lemma ledger (i:ℕ)(hi:i≤r)(x:X): born U K d r i x= U i x + ∑ j∈range i, ∑ n∈ range ((m j).toNat+1), motion (money K d j n) i * Assembly.jet (U j) n x := by
    rw [message K d r hp]; have h : range (i+1)⊆range (r+1):= Finset.range_mono (by omega)
    rw [← sum_subset h,sum_range_succ]
    · rw [add_comm,(paid r hp i hi).posted x]; simp_rw [this_step,one_mul]
    intro k hk ht; have hh : i < k:= by simp only [mem_range] at ht; omega
    simp_rw [triangular, if_neg hh.not_ge,zero_mul,sum_const_zero]
lemma apportion (i:ℕ)(hi:i≤r)(hy : ∀ j< i,m j≤ m i): Level (m i) (born U K d r i) := by
   rw [show born U K d r i= _ from funext (ledger K d r hp i hi)]
   refine (hp i hi).add (Level.total (f:=fun j x=> ∑ n∈ range ((m j).toNat+1), motion (money K d j n) i * Assembly.jet (U j) n x) _ fun j hj=> Level.total _ fun n hn=>?_)
   have hj:= mem_range.mp hj;have hh:= hp j (hj.le.trans hi)
   by_cases he : (m j)<n
   · rw [hh.jet n he]; simp only [Pi.zero_apply,mul_zero]; exact Level.zero _
   exact ((levelJet hh.smooth.contDiffAt n).factor _).promote ((le_of_not_gt he).trans (hy j hj)) -- neg note
lemma booked (i:ℕ) (t:ℕ) (hv:t≤r)(he:i≤t) : born U K d t i= born U K d r i := by
   funext x; rw [ledger K d t (m:=m) (fun i hi=> hp i (hi.trans hv)) _ he, ledger K d r hp i (he.trans hv)]
lemma reference (t:ℝ)(x:X) : cover (born U K d r) r t x=∑ i∈range (r+1),∑ j∈range ((m i).toNat+1), peval (motion (money K d i j)) r t * Assembly.jet (U i) j x:= by
   unfold cover peval Zone.eval; simp_rw [message K d r hp, Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _
   rw [sum_comm]; exact sum_congr rfl fun j _=> by simp [Finset.sum_mul,Complex.real_smul,mul_assoc]
end YM.Comparison.RG02.Adjacent
