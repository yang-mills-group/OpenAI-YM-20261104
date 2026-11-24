import YM.Integration.WilsonUniformUnmarkedHessianRow

/-! All occupied finite field tensors in the genuine anchored weighted
sum: order, differentiating field, and all old coordinates are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedTensorRows
open Filter Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorBulkHistory
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators ContDiff Matrix

variable {G : Gauge} {n : Side} {I : Type} [Fintype I] [DecidableEq I]

theorem listDerivative (P : MvPolynomial I ℝ) (l : List I) :
    Whisk.read 0 l P=(l.length.factorial:ℝ)*marble l.length P l.get := by
  let f:=CrossH.clue P
  have smooth : ContDiffAt ℝ (↑l.length) f 0 := (Cacao.vent P).contDiffAt.of_le le_top
  have h:=CrossH.chain f l l.length 0 smooth le_rfl
  have row:=congrFun (WilsonConditionalTaylorFiniteHessian.tensor P l.length) l.get
  change (l.length.factorial:ℝ)⁻¹*iteratedFDeriv ℝ l.length f 0 (dotI ∘ l.get)=_ at row
  rw [←CrossH.tours 0 P l,h,←row,←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
  rfl

theorem tupleDerivative (P : MvPolynomial I ℝ) {r : ℕ} (i : I) (t : Fin r→I) :
    Whisk.read 0 (List.ofFn t) (MvPolynomial.pderiv i P)=
      ((r+1).factorial:ℝ)*marble (r+1) P (Fin.cons i t) := by
  have transport {u v : ℕ} (b : Fin u→I) (c : Fin v→I) (len : u=v)
      (same : ∀ j,b j=c (j.cast len)) : marble u P b=marble v P c := by
    subst v
    have same' : b=c :=funext same
    exact congrArg (marble u P) same'
  let v : Fin (r+1)→I := Fin.cons i t
  have matchRow : marble (List.ofFn v).length P (List.ofFn v).get=marble (r+1) P v :=
    transport _ _ List.length_ofFn (fun j=>List.get_ofFn ..)
  rw [←Whisk.read_next 0 i,←List.ofFn_cons]
  change Whisk.read 0 (List.ofFn v) P=_
  rw [listDerivative,matchRow,List.length_ofFn]

omit [DecidableEq I] in
theorem yarn (r : ℕ) (f : List I→ℝ) :
    Whisk.Yarn r f=∑ t : Fin r→I,f (List.ofFn t) := by
  induction r generalizing f with
  | zero => simp [Whisk.Yarn]
  | succ r ih =>
    rw [Whisk.twilled]
    simp_rw [ih]
    rw [←(Fin.consEquiv (fun _ : Fin (r+1)=>I)).sum_comp (fun t=>f (List.ofFn t)),Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro t _
    simp

theorem entry (A : Pap (wire G n)) {e : ℕ} (pos : 0<e) {r : ℕ} (q : Fin r→wire G n) :
    marble r (coeff e (WilsonConditionalTaylorRawAttachment.stored A))
      ((WilsonMovingGaussianCoordinates.link G n).symm ∘ q) = rancho A e r q := by
  unfold WilsonConditionalTaylorRawAttachment.stored
  rw [WilsonConditionalTaylorFieldReset.positive _ pos]
  let E:=WilsonMovingGaussianCoordinates.link G n
  change marble r (MvPolynomial.rename E.symm (coeff e A)) _=_
  rw [Shore.pebble,Shore.cores_once]
  apply congrArg (marble r (coeff e A))
  funext i;exact E.apply_symm_apply (q i)

def weight (n : Side) (G : Gauge) {r : ℕ} (i : wire G n) (t : Fin r→wire G n) (σ : ℝ) (s : ℕ) :=
  let E:=(WilsonMovingGaussianCoordinates.link G n).symm
  let l:=Measuring.chart n G
  Whisk.spread l {l (E i)} σ s (List.ofFn (E ∘ t))

theorem charges (A : Pap (wire G n)) (i : wire G n) (σ : ℝ) (s e r : ℕ) (pos : 0<e) :
    (∑ t : Fin r→wire G n, weight n G i t σ s *
      |((r+1).factorial:ℝ)*rancho A e (r+1) (Fin.cons i t)|) =
      CrossH.cog (Measuring.chart n G) σ s (coeff e (WilsonConditionalTaylorRawAttachment.stored A)) r
        ((WilsonMovingGaussianCoordinates.link G n).symm i) := by
  let E:=(WilsonMovingGaussianCoordinates.link G n).symm
  let F:=coeff e (WilsonConditionalTaylorRawAttachment.stored A)
  let l:=Measuring.chart n G
  let b:=fun t : Fin r→Primary n G=>Whisk.rate l {l (E i)} σ s 0 (MvPolynomial.pderiv (E i) F) (List.ofFn t)
  change _=Whisk.Yarn r (Whisk.rate l {l (E i)} σ s 0 (MvPolynomial.pderiv (E i) F))
  rw [yarn]
  change _ = ∑ t : Fin r→Primary n G,b t
  let into: (Fin r→wire G n)≃(Fin r→Primary n G):=Equiv.arrowCongr (Equiv.refl (Fin r)) E
  rw [←into.sum_comp b]
  apply Finset.sum_congr rfl;intro t _
  change _=weight n G i t σ s*|Whisk.read 0 (List.ofFn (E ∘ t)) (MvPolynomial.pderiv (E i) F)|
  have scatter : Fin.cons (E i) (E ∘ t)=E ∘ Fin.cons i t := by
    funext k;refine Fin.cases ?_ (fun z=>?_) k <;> rfl
  rw [tupleDerivative,scatter,entry A pos]

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include bought simple in
theorem bounded (s p : ℕ) (hs : 6 ≤ s) {η : ℝ} (fee : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N → ∀ e, 0<e → e ≤ p →
      ∀ r, r ≤ e+1 → let n:=R.family.side j per
      let A:=course R u wood tags N j n
      let σ:=Alto.candles R.family.path.levels j
      ∀ i : wire G n, (∑ t : Fin r→wire G n, weight n G i t σ s *
        |((r+1).factorial:ℝ)*rancho A e (r+1) (Fin.cons i t)|) ≤ (regulatorRun R.family N per j)^(-η) := by
  filter_upwards [WilsonUniformUnmarkedFiniteStrip.anchored R simple u V bought wood tags s p hs fee]
    with k bond N per kN j lo hi e pos cap r val n A σ i
  rw [charges A i σ s e r pos]
  exact bond N per kN j lo hi e cap r val _

end YM.Integration.WilsonUniformUnmarkedTensorRows
