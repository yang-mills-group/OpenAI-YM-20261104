import YM.Comparison.RG02.Adjacent.Transport
/-!
# Sale on the joint order/marker board

Compatible through taking logs, compensating vacuum coupling, mark adjustment by simple powers.
Readout's genuine field-basis recalibration not replaced by this. Use before/after that with
ratio uncertainty still present. Operates pointwise formal rescaled fields; costs NOT tested by
this combination.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice Marker Multi
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "φ"=> 𝓝 (0:ℝ)
local notation "λ₀"=> (ω:WithTop ℕ∞)
variable (K L : UnitCost) (d:V→ℤ) (r:ℕ) (s:R.Mode)
open Cumulants
open YM.Extra.Trajectories (connected)

namespace Trade
local notation "Q"=> Grade R r
def mark (d:V→ℤ)(x:ℝ) (i:V) : ℂ:= ↑(x^d i)
variable (R) in
def alter (t:ℝ) : Grade R r→ₐ[ℂ] Grade R r:= dilation (Board R r) (Sum.elim (mark d (K.rating t)) (fun _=> ↑(K.rating t)))
local notation "α"=> alter R K d r

variable (P:X→Grade R r) (x:X)
def course (t:ℝ) : Grade R r:= alter R K d r t (P ((K.rating t)⁻¹ • x))
def barter : Grade R r:= fuse R r (course K d r P x)

def read (P:X→Grade R r) (s:R.Mode)(j:ℕ)(x:X):= detail (P x) s j

def markDebt := ∑ i∈ s.val,d i
lemma hammers (p:Grade R r) (t:ℝ) (u:Index r): (alter R K d r t p).part (Join.pair s u)=(∏ i∈s.val, mark d (K.rating t) i)*(K.rating t:ℂ)^u.val.card * p.part (Join.pair s u) := by rw [alter,dilation_part]; simp [Join.pair]
lemma chosen (p:Grade R r) (t:ℝ) (hp:Order.Symmetric p) : Order.Symmetric (alter R K d r t p) := by
   apply Order.symmetric_test; intro s u v H; rw [hammers,hammers,← hp.observe_part,← hp.observe_part, H]
omit [Fintype V] in
private lemma remaining (x:ℝ) (h:x≠0) (s:Finset V) : ∏ i∈s, mark d x i= (↑ (x^(∑ i∈s, d i) : ℝ) : ℂ):= by
  induction s using Finset.induction with
  | empty=> simp
  | insert i u he ih=> rw [prod_insert he,sum_insert he,zpow_add₀ h,Complex.ofReal_mul,ih]; rfl
lemma tax (u:ℕ) (p:Grade R r) (t:ℝ) (he:K.rating t≠0) : detail (alter R K d r t p) s u= detail p s u * (↑(K.rating t ^ markDebt d s):ℂ) * (K.rating t:ℂ)^u := by
   unfold detail observe; split
   next hz=> simp_rw [Poly.part_smul]; change _*(( (alter R K d r t p)).part (Join.pair s _))=_; rw [hammers,picked r hz,remaining _ _ he]; unfold markDebt; change _* (_*_ *_)=(_* (p.part (Join.pair s (pick r u))))* _* _; ring
   next hz=> simp [Poly.part_nil]
lemma paying (t:ℝ) (hv : 0<K.rating t): (value (t:ℂ) (course K d r P x t)).part s=ages (read r P s) (markDebt d s) r t (K.rating t) x := by
   unfold course; rw [vpart]; change (∑ k∈ range (r+1), (t:ℂ)^k*detail _ s k)=_
   unfold ages cover read; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [tax K d r s i _ t hv.ne']; push_cast; ring
lemma stays_even (t:ℝ)(x:Grade R r): ((alter R K d r t x)).part ((Board R r).quiet)=x.part ((Board R r).quiet):= quiet_dilation _ _
lemma bottom_stays (t:ℝ)(x:Grade R r): alter R K d r t (denominator x)=denominator (alter R K d r t x):= by
   apply Join.both_parts; intro i u; simp_rw [hammers,denominator,bottom_value]; split_ifs with he; subst i; apply Eq.symm; apply hammers
   simp
lemma ratio_stays (t:ℝ)(x:Grade R r)(h:UnitLeading x): alter R K d r t (Order.ratio x)=Order.ratio (alter R K d r t x):= by
   apply Order.ratio_unique ((stays_even K d r t x).trans h); rw [← bottom_stays,← map_mul,recovers h]
lemma log_stays (t:ℝ)(x:Grade R r)(h:UnitLeading x): alter R K d r t (logMarked x)= logMarked (alter R K d r t x) := (Cumulants.log_map _ (stays_even K d r t) (ratio_quiet h)).trans (congrArg connected (ratio_stays K d r t x h))
lemma log_backs (t:ℝ)(x:Grade R r)(h:UnitLeading x): alter R K d r t (logVac x)= logVac (alter R K d r t x) := (Cumulants.log_map _ (stays_even K d r t) ((bottom_quiet x).trans h)).trans (congrArg connected (bottom_stays K d r t x))


structure Shows (A:X→Grade R r) : Prop where
 sold x : Order.Symmetric (A x)
 done (L:UnitCost) (x:X): Seen (fun t=> A ((L.rating t)⁻¹ • x))
 paid : ∀ x, UnitLeading (A x)
variable {P} (h : Shows r P)
variable {x}
namespace Shows
include h
lemma describes (x:X): Seen (course K d r P x):= by
   constructor; intro i
   have hc j: ContDiffAt ℝ ω (fun t=> mark d (K.rating t) j) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (K.spin _)
   rw [← Join.pair_reunite i]; simp_rw [course,hammers]
   exact ((contDiffAt_prod (fun i _=> hc i)).mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ K.smooth).pow _)).mul ((h.done K x).smooth _)
lemma leads {x:X}: ∀ᶠ t in φ, UnitLeading (course K d r P x t) := Eventually.of_forall fun t=> (stays_even K d r t _).trans (h.paid _)
lemma rolls (x:X) : UnitLeading (barter K d r P x):= fuse_leading (h.leads ..)
lemma sees (x:X): Order.Symmetric (barter K d r P x):= fuse_symmetric (Eventually.of_forall fun t=> chosen K d r _ t (h.sold ((K.rating t)⁻¹ • x)))
lemma goes (x:X) (j:ℕ)(hh:j≤ r): read r (barter K d r P) s j x=born (read r P s) K (markDebt d s) r j x := by
    let L:= h.describes K d r x
    have he t: Order.Symmetric ( (course K d r P x) t):= chosen K d r _ _ (h.sold _)
    unfold read barter born; rw [← valued L (Eventually.of_forall he) hh]; exact mgerm (K.bright.mono fun _ hw=> paying K d r s _ x _ hw)
omit h in
lemma knows {U : X→Grade R r} (s :∀x,Order.Symmetric (U x)) (he:∀i:(Board R r).Mode,ContDiff ℝ ω (fun x=> (U x).part i))
 (hx : ∀x,UnitLeading (U x)): Shows r U := ⟨s,fun K x=> ⟨fun i=> (he i).contDiffAt.comp (0:ℝ) ((K.smooth.inv (by rw [K.origin]; simp)).smul contDiffAt_const)⟩,hx⟩
lemma repaid (x:X): barter K d r (Order.ratio ∘ P) x=Order.ratio (barter K d r P x):= by
   unfold barter; rw [show course _ _ _ (Order.ratio ∘ P) x= Order.ratio ∘  (course K d r P x) from funext fun t=>ratio_stays K d r t _ (h.paid _)]; exact (fuse_ratio (h.describes ..) (h.leads ..)).2
lemma recorded (x:X) : barter K d r (logMarked ∘ P) x=logMarked (barter K d r P x):= by
   unfold barter; rw [show course _ _ _ (logMarked ∘ P) x= logMarked ∘  (course K d r P x) from funext fun t=>log_stays K d r t _ (h.paid _)]; exact (fuse_mark (h.describes ..) (h.leads ..)).2
lemma covered (x:X) : barter K d r (logVac ∘ P) x=logVac (barter K d r P x):= by
   unfold barter; rw [show course _ _ _ (logVac ∘ P) x= logVac ∘  (course K d r P x) from funext fun t=>log_backs K d r t _ (h.paid _)]; exact (fuse_vac (h.describes ..) (h.leads ..)).2
lemma utter (x:X)(j:ℕ)(hj:j≤ r): detail (logMarked (barter K d r P x)) s j=born (read r (logMarked ∘ P) s) K (markDebt d s) r j x:= by
   rw [← h.recorded K d r, barter]
   have ht : Seen (course K d r (logMarked ∘ P) x):= (fuse_mark (h.describes K d r x) (h.leads K d r)).1.changeOf (Eventually.of_forall fun t=> (log_stays K d r t _ (h.paid ((K.rating t)⁻¹ • x))).symm)
   rw [← valued ht (Eventually.of_forall fun t=> chosen K d r _ t (sym_logMarked (h.paid _) (h.sold ((K.rating t)⁻¹ • x)))) hj]; exact mgerm (K.bright.mono fun _ hv=> paying K d r s _ x _ hv)
lemma read_cost (x:X)(j:ℕ)(hj:j≤ r): detail (logVac (barter K d r P x)) R.quiet j=born (read r (logVac ∘ P) R.quiet) K 0 r j x:= by
   rw [← h.covered K d r, barter]
   have ht : Seen (course K d r (logVac ∘ P) x):= (fuse_vac (h.describes K d r x) (h.leads K d r)).1.changeOf (Eventually.of_forall fun t=> (log_backs K d r t _ (h.paid ((K.rating t)⁻¹ • x))).symm)
   -- h.quiet
   rw [← valued ht (Eventually.of_forall fun t=> chosen K d r _ t (sym_logVac (h.paid _) (h.sold ((K.rating t)⁻¹ • x)))) hj, ← show markDebt d R.quiet=0 from sum_empty]; exact mgerm (K.bright.mono fun _ hv=> paying K d r R.quiet _ x _ hv)
end Shows
end Trade
end YM.Comparison.RG02.Adjacent
