import YM.Integration.WilsonMatrixOriginalDeckPrescriptionGrowth

/-! Buy the full two-clock inverse and every causal transfer simultaneously before the lattice and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionCash
open PhysicalNext.Repeat.Legato Finset MS MS.Land MS.Menus MS.Local.Physical WilsonMatrixOriginalDeckPrescription
open WilsonMatrixOriginalDeckPrescriptionSeries WilsonMatrixOriginalDeckPrescriptionGrowth WilsonMatrixOriginalDeckRelative
open scoped Classical BigOperators Matrix
variable {G:Gauge} {B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

theorem registered (k:ℕ):Bound (fun μ _=>fees Q h μ k) ∧ Bound (fun _ ν=>fees Q h ν k):=by
  obtain ⟨C,hC,d,bill⟩:=WilsonMatrixOriginalDeckPrescriptionResolvent.price Q h k
  constructor
  · refine ⟨C,hC,d,?_⟩;intro μ ν
    exact (bill μ k le_rfl).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (show 1+‖μ‖≤ size μ ν by unfold size;linarith [norm_nonneg ν]) d) hC.le)
  · refine ⟨C,hC,d,?_⟩;intro μ ν
    exact (bill ν k le_rfl).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (show 1+‖ν‖≤ size μ ν by unfold size;linarith [norm_nonneg μ]) d) hC.le)

private theorem matrix_powers {T:Type*} [Fintype T] [DecidableEq T] {A:Accounts T}
    (paid:Bound A)(n:ℕ):Bound (fun μ ν=>(A μ ν)^n):=by
  induction n with
  | zero=>simpa only [pow_zero] using fixed (1:Matrix T T ℂ)
  | succ n ih=>simpa only [pow_succ] using multiply ih paid

private theorem finite_inverse {T:Type*} [Fintype T] [DecidableEq T] (n:ℕ) (A:Accounts T) (paid:Bound A)
    (finite:∀μ ν,(A μ ν)⁻¹=∑i∈Finset.range (n+1),(1-A μ ν)^i):
    Bound (fun μ ν=>(A μ ν)⁻¹):=by
  let K:Accounts T:=fun μ ν=>1-A μ ν
  have centered:Bound K:=minus (fixed (1:Matrix T T ℂ)) paid
  have bank:Bound (fun μ ν=>∑i∈Finset.range (n+1),(K μ ν)^i):=
    total _ (fun i μ ν=>(K μ ν)^i) (fun i _=>matrix_powers centered i)
  have eq:(fun μ ν=>(A μ ν)⁻¹)=(fun μ ν=>∑i∈Finset.range (n+1),(K μ ν)^i):=by funext μ ν;exact finite μ ν
  rw [eq];exact bank

theorem inverse:Bound (fun μ _=>(fees Q h μ 0)⁻¹):=
  finite_inverse h (fun μ _=>fees Q h μ 0) (registered Q h 0).1 (fun μ _=>WilsonMatrixOriginalDeckPrescriptionResolvent.geometric Q h μ)

theorem cost (k:ℕ):Bound (fun μ ν=>trial Q h μ ν k):=by
  induction k using Nat.strong_induction_on with
  | h n before =>
    have rest:=total (Finset.univ:Finset (Fin n)) (fun j μ ν=>fees Q h μ (n-j.val)*trial Q h μ ν j.val)
      (fun j _=>multiply (registered Q h (n-j.val)).1 (before j.val j.isLt))
    have bound:=multiply (inverse Q h) (minus (registered Q h n).2 rest)
    have eq:(fun μ ν=>trial Q h μ ν n)=(fun μ ν=>(fees Q h μ 0)⁻¹*(fees Q h ν n-∑j:Fin n,fees Q h μ (n-j.val)*trial Q h μ ν j.val)):=by
      funext μ ν;rw [trial]
    rw [eq];exact bound

/-- All coefficients through K share a single before-period polynomial in both absolute clocks. -/
theorem purchased (K:ℕ):∃C:ℝ,0<C ∧ ∃d:ℕ,∀μ ν:ℝ,∀k≤K,
    WilsonMatrixOriginalDeckRelative.amount (trial Q h μ ν k) ≤ C*(size μ ν)^d:=by
  have priced(j:Fin (K+1)):∃C:ℝ,0<C ∧ ∃d:ℕ,∀μ ν:ℝ,WilsonMatrixOriginalDeckRelative.amount (trial Q h μ ν j.val)≤C*(size μ ν)^d:=cost Q h j.val
  choose C positive degree bill using priced
  let cap:=Finset.univ.sup degree
  have nonnegative:0≤∑j,C j:=sum_nonneg fun j _=>(positive j).le
  refine ⟨1+∑j,C j,by linarith,cap,?_⟩;intro μ ν k hk
  let j:Fin (K+1):=⟨k,by omega⟩
  have charge:C j≤∑l,C l:=single_le_sum (fun l _=>(positive l).le) (mem_univ j)
  have lower:degree j≤cap:=Finset.le_sup (f:=degree) (Finset.mem_univ j)
  exact (bill j μ ν).trans (mul_le_mul (by linarith) (pow_le_pow_right₀ (size_ge μ ν) lower)
    (pow_nonneg (by linarith [size_ge μ ν]) _) (by linarith))

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionCash
