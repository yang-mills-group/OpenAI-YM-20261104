import YM.QuadraticLocal.Fusion
import YM.Integration.WilsonRootedForcedProfile

/-! A passive coefficient rides the actual merged pellet's original letters.
Both the constant and the radius-weighted first coefficient keep one prefield bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedFusionScratch
open Function Filter Finset Lattice Wilson RG Ac Marker
open Push.Corrected Push.AbsoluteSums MeasureTheory RG3 RG3.Ink Ovens Ovens.Pipes
open QuadraticLocal.Fusion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{X:Pipes G n}{p:BudgetPoint}
variable {V:Type*}[DecidableEq V]{R:Census V}{o:V → Site n}

def salary (w:V → ℝ)(ρ:ℝ)(f:Polynomial (Poly R)):ℝ:=
  Poly.price w (f.coeff 0)+ρ*Poly.price w (f.coeff 1)

theorem nonnegative (w:V → ℝ)(hw:∀v,0<w v){ρ:ℝ}(hr:0 ≤ ρ)(f:Polynomial (Poly R)):
    0 ≤ salary w ρ f:=add_nonneg (Poly.nonnegative hw _) (mul_nonneg hr (Poly.nonnegative hw _))

theorem multiply (w:V → ℝ)(hw:∀v,0<w v){ρ:ℝ}(hr:0 ≤ ρ)(f k:Polynomial (Poly R)):
    salary w ρ (f*k) ≤ salary w ρ f*salary w ρ k:=by
  unfold salary
  rw [Polynomial.mul_coeff_zero,Polynomial.mul_coeff_one]
  have a:=Poly.multiplication hw (f.coeff 0) (k.coeff 0)
  have b:Poly.price w (f.coeff 0*k.coeff 1+f.coeff 1*k.coeff 0) ≤ 
      Poly.price w (f.coeff 0)*Poly.price w (k.coeff 1)+Poly.price w (f.coeff 1)*Poly.price w (k.coeff 0):=
    (Poly.addition hw _ _).trans (add_le_add (Poly.multiplication hw ..) (Poly.multiplication hw ..))
  refine (add_le_add a (mul_le_mul_of_nonneg_left b hr)).trans ?_
  nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg ρ) (Poly.nonnegative hw (f.coeff 1))) (Poly.nonnegative hw (k.coeff 1))]

theorem product {ι:Type*}(w:V → ℝ)(hw:∀v,0<w v){ρ:ℝ}(hr:0 ≤ ρ)(S:Finset ι)(f:ι → Polynomial (Poly R)):
    salary w ρ (∏i∈S,f i) ≤ ∏i∈S,salary w ρ (f i):=by
  induction S using Finset.induction_on with
  | empty=>simp [salary,Polynomial.coeff_one]
  | insert i s absent ih=>
    simp only [prod_insert absent]
    exact (multiply w hw hr _ _).trans (mul_le_mul_of_nonneg_left ih (nonnegative w hw hr _))

def receipt (e:ℕ≃X.Pellet)(p:BudgetPoint)(f:Ovens.Label → Config G n → Polynomial (Poly R))(i:ℕ)(U:Config G n):Polynomial (Poly R):=
  if (addr e p i).eligible p.threshold U then ∏j∈(e i).val,f j U else 0

def income (e:ℕ≃X.Pellet)(c:Ovens.Label → ℝ)(i:ℕ):ℝ:=∏j∈(e i).val,c j

theorem constant (e:ℕ≃X.Pellet)(S:(layout X).Stock p R o)(f:Ovens.Label → Config G n → Polynomial (Poly R))
    (same:∀i U,(f i U).coeff 0=S.ink i U)(i:ℕ)(U:Config G n):
    (receipt e p f i U).coeff 0=Attached.marked e S i U:=by
  rw [receipt,Attached.marked_eq]
  split
  · simp only [Polynomial.coeff_zero_prod,same]
  · simp

theorem pension (R:Census V)(e:ℕ≃X.Pellet)(p:BudgetPoint){w:V → ℝ}(hw:∀i,0<w i)(c:Ovens.Label → ℝ)(positive:∀i,0 ≤ c i)
    {a χ γ:ℝ}(ha:0 ≤ a)(hx:1 ≤ χ)(hg:0 ≤ γ)
    (paid:Hit X.patch p.B (fun i=>Sum.elim (fun _=>χ) (fun _=>1) i*c i) (a+1) γ)
    (room:(p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1):
    Hit (fun i=>(addr e p i).support) p.B (income e c) a ((Real.exp γ-1)/χ):=by
  let f (i:Ovens.Label):Poly R:=(c i:ℂ) • 1
  have val(i:Ovens.Label):Poly.price w (f i)=c i:=by
    rw [show f i=(c i:ℂ) • (1:Poly R) from rfl,Poly.adapted,Poly.one_price,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive i)]
  have before:Hit X.patch p.B (fun i=>Sum.elim (fun _=>χ) (fun _=>1) i*Poly.price w (f i)) (a+1) γ:=by
    simpa only [val] using paid
  have after:=Attached.payment (p:=p) e hw ha hx hg before room
  have computed(i:ℕ):Poly.price w (Attached.wallet e f i)=income e c i:=by
    change Poly.price w (∏j∈(e i).val,(c j:ℂ) • (1:Poly R))=∏j∈(e i).val,c j
    rw [Finset.prod_smul,prod_const_one,Poly.adapted,Poly.one_price,mul_one,norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive j)]
  simpa only [computed] using after

theorem paid (e:ℕ≃X.Pellet)(p:BudgetPoint){w:V → ℝ}(hw:∀i,0<w i){ρ:ℝ}(hr:0<ρ)
    (f:Ovens.Label → Config G n → Polynomial (Poly R))(c:Ovens.Label → ℝ)(pos:∀i,0 ≤ c i)
    (cap:∀i U,salary w ρ (f i U) ≤ c i){a χ γ:ℝ}(ha:0 ≤ a)(hx:1 ≤ χ)(hg:0 ≤ γ)
    (fund:Hit X.patch p.B (fun i=>Sum.elim (fun _=>χ) (fun _=>1) i*c i) (a+1) γ)
    (room:(p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1):
    Hit (fun i=>(addr e p i).support) p.B (income e c) a ((Real.exp γ-1)/χ) ∧
    (∀i U,salary w ρ (receipt e p f i U) ≤ income e c i) ∧
    ∀i U,Poly.price w ((receipt e p f i U).coeff 1) ≤ (income e c i)/ρ:=by
  have bill(i:ℕ)(U:Config G n):salary w ρ (receipt e p f i U) ≤ income e c i:=by
    unfold receipt
    split
    · exact (product w hw hr.le _ _).trans (Finset.prod_le_prod (fun j _=>nonnegative w hw hr.le _) (fun j _=>cap j U))
    · simpa [salary,income] using Finset.prod_nonneg (s:=(e i).val) (f:=c) (fun j _=>pos j)
  refine ⟨pension R e p hw c pos ha hx hg fund room,bill,fun i U=>?_⟩
  apply (le_div_iff₀ hr).2
  rw [mul_comm]
  exact (le_add_of_nonneg_left (Poly.nonnegative hw _)).trans (bill i U)
end YM.Integration.WilsonRootedFusionScratch
