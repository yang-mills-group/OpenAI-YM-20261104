import YM.Integration.WilsonVacuumPreResetMeasuredCaliber
import YM.LocalLTE.Weft.Fabric

/-! Signed radial evaluation of the original inverse-coupling chart.
The purchased pupil only has to agree on the tested real line, through
the retained degrees. The finite radial identity follows the original
WilsonPosteriorProjectionReexpressionRadial.recorded and
WilsonMarkedPolynomialRebooking.complete calculations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralSignedPolynomialRate
open Function Filter Finset LocalLTE.Weft Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Order Comparison.RG02.Adjacent Comparison.RG02.Moving.Path Comparison.RG02.Moving.Shift
open PertExtension.Series PertExtension.Series.Tested
open Finset PowerSeries MvPolynomial FormalBulk08 Wine Orb
open WilsonMarkedKineticDefect
open scoped Classical BigOperators ContDiff
variable {E ι:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def Shape (U : Display E) (p : ℕ) (m : ℕ → ℕ) (z : E)
    (a : ∀ i, J (m i) → ℂ) : Prop :=
  ∀ i ≤ p, ∀ t : ℝ, U i (t • z) = ∑ j, t^j.val • a i j

private theorem ages_on_line (U : Display E) (d : ℤ) (p : ℕ) (m : ℕ → ℕ) (z : E)
    (a : ∀ i, J (m i) → ℂ) (shape : Shape U p m z a) (t u : ℝ) :
    ages U d p t u z = ∑ i ∈ range (p+1), ∑ j : J (m i),
      ((t:ℂ)^i * (tags d i j.val u:ℂ)) * a i j := by
  unfold ages cover
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [shape i (mem_range_succ_iff.mp hi),mul_sum,mul_sum]
  apply sum_congr rfl
  intro j _
  unfold tags
  rw [Complex.real_smul]
  push_cast
  ring

/-- The original nonlinear coupling/field motion from the exact
one-dimensional formula, with no smoothness assumption on the field
family away from its tested line. -/
theorem recorded (U : Display E) (K : UnitCost) (d : ℤ) (p r : ℕ) (m : ℕ → ℕ)
    (z : E) (a : ∀ i, J (m i) → ℂ) (shape : Shape U p m z a) :
    born U K d p r z = ∑ i ∈ range (p+1), ∑ j : J (m i),
      motion (money K d i j.val) r * a i j := by
  unfold born
  simp_rw [ages_on_line U d p m z a shape]
  let f (i : ℕ) (j : J (m i)) (t : ℝ) := money K d i j.val t * a i j
  have smooth (i : ℕ) (j : J (m i)) : ContDiffAt ℝ ω (f i j) 0 :=
    (monetized K d i j.val).mul contDiffAt_const
  change motion (fun t => ∑ i ∈ range (p+1), ∑ j : J (m i), f i j t) r = _
  rw [msum (f:=fun i t => ∑ j : J (m i), f i j t) _ fun i _ =>
    ContDiffAt.sum fun j _ => smooth i j]
  apply sum_congr rfl
  intro i _
  rw [msum _ _ fun j _ => smooth i j]
  apply sum_congr rfl
  intro j _
  unfold f
  rw [show (fun t => money K d i j.val t * a i j) = _ from
    funext (fun t => mul_comm (money K d i j.val t) (a i j)),mul_comm _ (a i j)]
  exact mscale _ (monetized K d i j.val)

omit [Fintype ι] in
private theorem homogeneous_ray (x:ℝ)(v:ι→ℝ)(n:ℕ)(F:MvPolynomial ι ℝ) : MvPolynomial.eval (x •v) (homogeneousComponent n F)= x^n* MvPolynomial.eval v (homogeneousComponent n F):=by
    let S:=homogeneousComponent n F; have ht: S.IsHomogeneous n:= homogeneousComponent_isHomogeneous ..;  change MvPolynomial.eval _ S=x^n*MvPolynomial.eval v S; rw [← S.support_sum_monomial_coeff]; rw [map_sum,map_sum,mul_sum]; refine Finset.sum_congr rfl (fun i hi=> ?_); simp only [eval_monomial,Finsupp.prod,Pi.smul_apply, smul_eq_mul,mul_pow, Finset.prod_mul_distrib,prod_pow_eq_pow_sum]; have hv:=ht.degree_eq_sum_deg_support hi; rw [←hv]; ring
omit [Fintype ι] in
private theorem decomposition (n:ℕ)(F:MvPolynomial ι ℝ)(h:F.totalDegree ≤n) : (∑ i∈range (n+1), homogeneousComponent i F) = F:=by refine Eq.trans (sum_subset (range_mono (Nat.succ_le_succ h)) (fun i _ hi=> ?_)).symm (sum_homogeneousComponent F); exact homogeneousComponent_eq_zero i F (by simpa only [mem_range, Nat.lt_succ_iff,not_le] using hi)

theorem component (A B:Pence) (T:Pap ι) (e q:ℕ) :
    homogeneousComponent q (coeff e (Wine.canter A B ι T)) =
      ∑ j∈range (e+1), Wine.bill A B e j q • homogeneousComponent q (coeff j T) := by
  rw [(Wine.steam A B (FormalBulk08.Series.dict T e)).apex,map_sum,map_sum,map_sum]
  apply sum_congr rfl
  intro j hj
  exact Wine.term_read A B j q e _ (Nat.le_of_lt_succ (mem_range.mp hj))

omit [Fintype ι] in
theorem levels (M:ℕ) (P:MvPolynomial ι ℝ) (bound:P.totalDegree≤2*M) (v:ι→ℝ) (t:ℝ) :
    (MvPolynomial.eval (t • v) P : ℂ) =
      ∑ q:J M,t^q.val • (MvPolynomial.eval v (homogeneousComponent q.val P) : ℂ) := by
  have expand := congrArg (MvPolynomial.eval (t • v)) (decomposition (2*M) P bound)
  rw [map_sum] at expand
  have real : MvPolynomial.eval (t • v) P =
      ∑ q:J M,t^q.val*MvPolynomial.eval v (homogeneousComponent q.val P) := by
    rw [Fin.sum_univ_eq_sum_range (fun q:ℕ=>t^q*MvPolynomial.eval v (homogeneousComponent q P)) (2*M+1)]
    simpa only [homogeneous_ray t] using expand.symm
  rw [real,Complex.ofReal_sum]
  apply sum_congr rfl
  intro q _
  rw [Complex.ofReal_mul,Complex.real_smul]

theorem evaluated (A B:Pence) (T:Pap ι) (v:ι→ℝ) (e q:ℕ) :
    (MvPolynomial.eval v (homogeneousComponent q (coeff e (Wine.canter A B ι T))) : ℂ) =
      ∑ j∈range (e+1),(Wine.bill A B e j q : ℂ)*(MvPolynomial.eval v (homogeneousComponent q (coeff j T)):ℂ) := by
  rw [component,map_sum,Complex.ofReal_sum]
  apply sum_congr rfl
  intro j _
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,Complex.ofReal_mul]

def read (L:E→ₗ[ℝ](ι→ℝ)) (T:Pap ι) (j:ℕ) (x:E) : ℂ :=
  MvPolynomial.eval (L x) (PowerSeries.coeff j T)

private theorem plain {K:UnitCost} {cap:ℕ} {H:Pence} (fee:∀e≤cap,∀j r,Moving.Path.motion (money K 0 j r) e=formalWeight H e j r)
    (L:E→ₗ[ℝ](ι→ℝ)) (T:Pap ι) {p e:ℕ} (he:e≤cap) (hp:e≤p) (z:E) :
    born (read L T) K 0 p e z =
      read L (canter (bookH H) (bookU H) ι T) e z := by
  let W := canter (bookH H) (bookU H) ι T
  let M := (PowerSeries.coeff e W).totalDegree +
    ∑ j∈range (p+1),(PowerSeries.coeff j T).totalDegree
  have hi (j:ℕ) (hj:j≤p) : (PowerSeries.coeff j T).totalDegree≤2*M := by
    have sub := single_le_sum (fun i (_:i∈range (p+1))=>Nat.zero_le ((PowerSeries.coeff i T).totalDegree))
      (show j∈range (p+1) by simpa using hj)
    dsimp only [M]
    omega
  have hw : (PowerSeries.coeff e W).totalDegree≤2*M := by
    dsimp only [M]
    omega
  let a (j:ℕ) (q:J M) : ℂ :=
    MvPolynomial.eval (L z) (homogeneousComponent q.val (PowerSeries.coeff j T))
  have shape : Shape (read L T) p (fun _=>M) z a := by
    intro j hj t
    unfold read
    rw [map_smul]
    exact levels M _ (hi j hj) (L z) t
  rw [recorded (read L T) K 0 p e (fun _=>M) z a shape]
  have price (j:ℕ) (q:J M) :
      Moving.Path.motion (money K 0 j q.val) e = formalWeight H e j q.val :=
    fee e he j q.val
  simp_rw [price]
  have part : range (e+1) ⊆ range (p+1) := range_mono (Nat.succ_le_succ hp)
  rw [←sum_subset part (fun j _ off=> by
     have beyond : ¬j≤e := by simpa using off
     simp [formalWeight,beyond])]
  have cut (j:ℕ) (hj:j∈range (e+1)) (q:J M) :
      formalWeight H e j q.val = (Wine.bill (bookH H) (bookU H) e j q.val : ℂ) := by
    rw [formalWeight,if_pos (Nat.le_of_lt_succ (mem_range.mp hj))]
  calc
    _ = ∑ j∈range (e+1),∑ q:J M,
        (Wine.bill (bookH H) (bookU H) e j q.val : ℂ)*a j q := by
      apply sum_congr rfl
      intro j hj
      simp_rw [cut j hj]
    _ = ∑ q:J M,∑ j∈range (e+1),
        (Wine.bill (bookH H) (bookU H) e j q.val : ℂ)*a j q := sum_comm
    _ = ∑ q:J M,(MvPolynomial.eval (L z) (homogeneousComponent q.val (PowerSeries.coeff e W)) : ℂ) := by
      apply sum_congr rfl
      intro q _
      exact (evaluated (bookH H) (bookU H) T (L z) e q.val).symm
    _ = read L W e z := by
      simpa [read] using (levels M (PowerSeries.coeff e W) hw (L z) 1).symm


theorem original {K:UnitCost}{cap:ℕ}{H:Pence}
    (fee:∀e≤cap,∀j r,Moving.Path.motion (money K 0 j r) e=formalWeight H e j r)
    (U:Display E)(L:E→ₗ[ℝ](ι→ℝ))(T:Pap ι){p e:ℕ}(he:e≤cap)(hp:e≤p)(z:E)(scale:ℂ)
    (paid:∀j≤p,∀t:ℝ,U j (t • z)=scale*read L T j (t • z)):
    born U K 0 p e z=scale*read L (canter (bookH H) (bookU H) ι T) e z:=by
  let M:=∑ j∈range (p+1),(PowerSeries.coeff j T).totalDegree
  let a (j:ℕ)(q:J M):ℂ:=MvPolynomial.eval (L z) (homogeneousComponent q.val (PowerSeries.coeff j T))
  have shape:Shape (read L T) p (fun _=>M) z a:=by
    intro j hj t
    unfold read
    rw [map_smul]
    apply levels
    have bound:=(single_le_sum (fun i (_:i∈range (p+1))=>Nat.zero_le ((PowerSeries.coeff i T).totalDegree))
      (show j∈range (p+1) by simpa using hj))
    dsimp only [M]
    omega
  have whole:Shape U p (fun _=>M) z (fun j q=>scale*a j q):=by
    intro j hj t
    rw [paid j hj t,shape j hj t,mul_sum]
    apply sum_congr rfl
    intro q _
    rw [Complex.real_smul,Complex.real_smul]
    ring
  calc
    _=scale*born (read L T) K 0 p e z:=by
      rw [recorded U K 0 p e (fun _=>M) z _ whole,recorded (read L T) K 0 p e (fun _=>M) z _ shape]
      simp only [Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro q _
      ring
    _=_:=congrArg (scale*·) (plain fee L T he hp z)

end YM.Integration.WilsonNeutralSignedPolynomialRate
end
