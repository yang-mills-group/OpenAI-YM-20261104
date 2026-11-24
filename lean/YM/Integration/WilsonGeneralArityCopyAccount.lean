import YM.Integration.WilsonGeneralArityBlockTable

/-! The issued compact words are actual group functions, with all angular ranks and the scalar rank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeneralArityCopyAccount
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor
open QuadraticLocal.Affinity QuadraticLocal.Sunrise Push Push.AbsoluteSums Paths Animals ConnectedActivityE6
open WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada WilsonRegisteredPairUnaryWallet
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{q d:ℕ}{σ:ℝ} (T:Copy G d q σ) (site:Site n)
local notation "S" => WilsonOlderFreshGraphPointWallet.point site
local notation "M" => T.rows (S) disk
local notation "Y" z:max => ((T.roll (z).1).leg (z).2.1)

def term (y:ℝ)(U:Config G n)(z:T.Roster):ℂ:=
  (y^((z.1.val:ℤ)-(Y z).r)*(Y z).atom.unmasked U site:ℝ)

private theorem ranks (z:T.Roster):(Y z).r<q+d+3:=by
  have h:(Y z).r+(Y z).roots.length ≤ z.1.val+d+2:=((T.paid z.1).pinned z.2.1).tall
  have room:=z.1.isLt
  omega

def cap (q d:ℕ)(y:ℝ):ℝ:=∑ j:Fin (q+1), ∑ r:Fin (q+d+3),
  |y^((j.val:ℤ)-r.val)| *2^r.val

theorem absolute (s₀:0 ≤ σ)(y:ℝ)(U:Config G n):Summable (term T site y U):=by
  have total:=WilsonOlderFreshGraphVote.before_tests (S) T.roll T.fare σ T.paid T.legal T.positive
    (value disk) s₀
  have height(z:T.Roster):(Y z).atom.magnitude  ≤  ((M) z).height σ:=by
    have mag:(Y z).atom.magnitude  ≤  ((M) z).salary:=by
      change _  ≤  (Y z).atom.magnitude*Real.exp (σ*(Y z).atom.length)
      exact le_mul_of_one_le_right z.2.property.le (Real.one_le_exp (mul_nonneg s₀ (Nat.cast_nonneg _)))
    exact mag.trans (le_mul_of_one_le_right ((M) z).sound.le
      (Real.one_le_exp (mul_nonneg s₀ (Nat.cast_nonneg _))))
  apply Summable.of_norm_bounded (total.2.1.mul_left (cap q d y))
  intro z
  let rank:Fin (q+d+3):=⟨(Y z).r, ranks T z⟩
  have all(j:Fin (q+1)) (r:Fin (q+d+3)):0 ≤ |y^((j.val:ℤ)-r.val)| *(2:ℝ)^r.val:=
    mul_nonneg (abs_nonneg _) (by positivity)
  have oneWeight: |y^((z.1.val:ℤ)-(Y z).r)| *2^(Y z).r  ≤  cap q d y:=
    (single_le_sum (fun r _=>all z.1 r) (mem_univ rank)).trans
      (single_le_sum (fun j _=>Finset.sum_nonneg (fun r _=>all j r)) (mem_univ z.1))
  rw [term,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  calc
    _  ≤  |y^((z.1.val:ℤ)-(Y z).r)| *((Y z).atom.magnitude*2^(Y z).r) :=
      mul_le_mul_of_nonneg_left ((Y z).atom.unmasked_bound U site) (abs_nonneg _)
    _ = (|y^((z.1.val:ℤ)-(Y z).r)| *2^(Y z).r)*(Y z).atom.magnitude := by ring
    _  ≤  _ := mul_le_mul oneWeight (height z) z.2.property.le (by unfold cap; positivity)

theorem original (s₀:0 ≤ σ) {ord seats shelf:ℕ} (deg:q ≤ ord) (occupied:1 ≤ seats) (fit:d ≤ shelf):
    let fee:=1+T.cost (S)
    Scene.Armada (M) (fun _=>1) (fun _=>d) σ fee ord seats shelf ∧
    (∀z,((M) z).binder=(S)) ∧
    (∀z,∃c:ℂ,∀a:Wallet disk,((M) z).paint a=c*WilsonThermometerRegisteredCapturedSector.amplitude disk a) ∧
    ∀(y:ℝ)(x:Wallet disk)(U:Config G n),HasSum (fun z=>((M) z).nominal y x U)
      ((x ()).val*∑'z:T.Roster,term T site y U z):=by
  intro fee
  have total:=WilsonOlderFreshGraphVote.before_tests (S) T.roll T.fare σ T.paid T.legal T.positive (value disk) s₀
  have plus:0 ≤ T.cost (S):=budget_nonneg total
  have bought:Scene.Armada (M) (fun _=>1) (fun _=>d) σ fee ord seats shelf:=
    T.earnings (S) disk s₀ (fun t=>(t ()).property) 1 fee zero_lt_one (by dsimp [fee];linarith)
      (by dsimp [fee];linarith) deg occupied fit
  refine ⟨bought,fun _=>rfl,fun _=>⟨_,fun _=>rfl⟩,?_⟩
  intro y x U
  have read:=(absolute T site s₀ y U).hasSum.mul_left (x ()).val
  exact read.congr_fun fun z=>T.group (S) disk x y U z

end YM.Integration.WilsonGeneralArityCopyAccount
end
