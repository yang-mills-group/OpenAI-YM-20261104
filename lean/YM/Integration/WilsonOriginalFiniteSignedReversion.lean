import YM.Integration.WilsonNeutralSignedPolynomialRate

/-! Revert the complete signed original marked roster on the actual radial price.
The individual convexity, real coordinates and degrees are taken before summing the
complex tests. The same measured inverse clock acts on every term of the old log. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiniteSignedReversion
open Function Filter Finset LocalLTE.Weft Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Order Comparison.RG02.Adjacent Comparison.RG02.Moving.Path Comparison.RG02.Moving.Shift
open PertExtension.Series PertExtension.Series.Tested
open Finset PowerSeries MvPolynomial FormalBulk08 Wine Orb
open WilsonMarkedKineticDefect WilsonNeutralSignedPolynomialRate
open scoped Classical BigOperators ContDiff
variable {E ι A:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype A]

theorem original {K:UnitCost}{cap:ℕ}{H:Pence}
    (fee:∀e≤cap,∀j q,Moving.Path.motion (money K 0 j q) e=formalWeight H e j q)
    (U:Display E)(L:E→ₗ[ℝ](ι→ℝ))(T:A→Pap ι)(a:A→ℂ){p e:ℕ}(he:e≤cap)(hp:e≤p)(z:E)
    (paid:∀j≤p,∀t:ℝ,U j (t • z)=∑b,a b*read L (T b) j (t • z)):
    born U K 0 p e z=∑b,a b*read L (canter (bookH H) (bookU H) ι (T b)) e z:=by
  let M:=∑b,∑ j∈range (p+1),(PowerSeries.coeff j (T b)).totalDegree
  let c (b:A)(j:ℕ)(q:J M):ℂ:= MvPolynomial.eval (L z) (homogeneousComponent q.val (PowerSeries.coeff j (T b)))
  have shape (b:A):Shape (read L (T b)) p (fun _=>M) z (c b):=by
    intro j hj t
    unfold WilsonNeutralSignedPolynomialRate.read
    rw [map_smul]
    apply WilsonNeutralSignedPolynomialRate.levels
    have h₁:=single_le_sum (fun i (_:i∈range (p+1))=>Nat.zero_le ((PowerSeries.coeff i (T b)).totalDegree))
      (show j∈range (p+1) by simpa using hj)
    have h₂:=single_le_sum (s:=Finset.univ) (fun b (_:b∈(Finset.univ:Finset A))=>
      Nat.zero_le (∑j∈range (p+1),(PowerSeries.coeff j (T b)).totalDegree)) (mem_univ b)
    dsimp only [M]
    omega
  have whole:Shape U p (fun _=>M) z (fun j q=>∑b,a b*c b j q):=by
    intro j hj t
    rw [paid j hj t]
    simp_rw [fun b=>shape b j hj t,Finset.mul_sum,Finset.smul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro b _
    rw [mul_smul_comm]
  let price (j:ℕ)(q:J M):ℂ:=Moving.Path.motion (money K 0 j q.val) e
  have inside (j:ℕ):(∑q:J M,price j q*(∑b,a b*c b j q))=
      ∑b,a b*(∑q:J M,price j q*c b j q):=by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm (price j _) (a _)]
  calc
    _ = ∑ j∈range (p+1),∑q:J M,price j q*(∑b,a b*c b j q):=recorded U K 0 p e _ z _ whole
    _ = ∑b,a b*(∑ j∈range (p+1),∑q:J M,price j q*c b j q):=by
      simp_rw [inside]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _:=by
      apply sum_congr rfl
      intro b _
      apply congrArg (a b*·)
      rw [←recorded (read L (T b)) K 0 p e _ z _ (shape b)]
      simpa only [one_mul] using WilsonNeutralSignedPolynomialRate.original fee (read L (T b)) L (T b) he hp z 1 (fun _ _ _=>by rw [one_mul])

end YM.Integration.WilsonOriginalFiniteSignedReversion
