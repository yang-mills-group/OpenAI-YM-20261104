import YM.QuadraticLocal.Tint.Ever
/-!
 # Complex costs at the cluster in Phase. Computational κ_REAL paints
   combine to the nominal ℂ before analysis. Keep charges EACH sign separately. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger Patrol
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b k τ:ℝ} {s i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X)
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} (T:Incoming P U α J R) (w:V→ℝ)(hw:∀ i,0<w i)
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Pressure
namespace Campus
local notation "K"=> Club.Keys X C
variable (σ:Patrol.Signs X C)
namespace Hearth
namespace Week
local notation "E₀"=> (Week.fuel X C σ)
local notation "χ₀"=> (Week.pack X C w)
open QuadraticLocal
variable (x:α)
include hw
variable [Countable ι] -- before theorem? functions Week.pack uses? definition Lean may not include instance. check
local notation "V₀" i:max=> (X (Club.stamp X C i))
local notation "Π"=> Poly.toll w (Club.alliance X C)
local notation "Φ"=> Club.stamp X C

lemma fortune : Week.pack X C w = Π *∏ i∈ C.val,(X i).salary:=by
    unfold Week.pack Week.chip Enroll.fare; rw [Finset.prod_mul_distrib]; change _ * ∏ i:Club.Keys X C,(X (Club.stamp X C i)).salary = _; rw [Club.product X C (fun i=>Poly.toll w (X i).mode),Club.product X C (fun i=>(X i).salary), Club.union_price]
lemma economize (a:ℝ)(ha:0≤a): Week.pack X C w ≤ Accumulate.rootPrice X w a C:= by
   unfold Week.pack; rw [Accumulate.rootPrice]; rw [show Week.chip X C w=(fun i=> Poly.toll w ((V₀ i).mode)*(X (Φ i)).salary) from rfl, Club.product X C (fun i=> Poly.toll w ((X i).mode)*(X i).salary)]; apply Finset.prod_le_prod; intro i _; exact mul_nonneg (Poly.worth hw _).le (X i).sound.le
   intro i _; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (X i).sound.le (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))) (Poly.worth hw _).le
-- PitchW.PC.K coherence is true germ off hull available via Lesson; don't deduce SUP cross-antibiotic.
lemma ticketΓ : ∑ s:Patrol.Signs X C, Patrol.price X C w s * ((Week.pack X C w *Week.fuel X C s x :ℝ):ℂ) = ∏ i∈ C.val,(X i).paint x:=by
   let f(i:Club.Keys X C)(b:Bool):ℂ:= Trigger.lens b* (↑(Trigger.slice b ((X (Club.stamp X C i)).paint x)):ℂ)
   have ht(i: Signs X C) : price X C w i * ((Week.pack X C w* Week.fuel X C i x:ℝ):ℂ)=∏ j:Club.Keys X C,f j (i j):=by
       rw [Week.fortune X C w hw,← Club.product X C (fun i=>(X i).salary)]; unfold price Week.fuel; have hp:(↑(Poly.toll w (Club.alliance X C)):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (Poly.worth hw _).ne';
       push_cast; rw [show ((Π:ℂ)⁻¹*photon X C i)*((Π:ℂ)*(∏ j, (↑((X (Club.stamp X C j)).salary):ℂ)) * ∏ j,(↑(Week.touch X C i x j):ℂ))= (photon X C i)* ((∏ j, (↑((X (Club.stamp X C j)).salary):ℂ))*(∏ j,(↑(Week.touch X C i x j):ℂ))) from (by field_simp)]
       unfold Patrol.photon; rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; unfold f; congr 1; let k:=(X (Φ j)); change ((k.salary:ℂ) * ( (Trigger.slice (i j) (k.paint x)/k.salary:ℝ):ℂ))=_; have he : (↑k.salary:ℂ)≠0:= Complex.ofReal_ne_zero.mpr k.sound.ne'; push_cast; field_simp; rfl
   simp_rw [ht]; rw [← Fintype.prod_sum f,← Club.product X C (fun i=>(X i).paint x)]; apply Finset.prod_congr rfl; intro i _; simp [f,Trigger.lens,Trigger.slice,add_comm]; rw [mul_comm Complex.I,Complex.re_add_im]
end Week
end Hearth
end Campus
end YM.QuadraticLocal.Tint
