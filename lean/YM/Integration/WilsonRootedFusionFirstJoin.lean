import YM.Integration.WilsonRootedFusionScratch
import YM.Integration.WilsonRootedHardAddressTariff
import Mathlib.Algebra.Polynomial.Derivative

/-! Keep the site on the original hard letter. Select merger words meeting the
named external letter while it is still in the true connected original pellet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedFusionFirstJoin
open Function Filter Finset Lattice Wilson RG Ac Marker
open Push.Corrected Push.AbsoluteSums MeasureTheory RG3 RG3.Ink Ovens Ovens.Pipes
open QuadraticLocal.Fusion WilsonRootedFusionScratch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{X:Pipes G n}{p:BudgetPoint}
variable {V:Type*}[DecidableEq V]{R:Census V}{o:V → Site n}

def dye (X:Pipes G n)(f:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(j:Ovens.Label)(U:Config G n):Poly R:=
  j.elim (fun i => ∑x∈(X.kernel i).support,h x • f i x U) (fun _ => 0)

def letters (S:(layout X).Stock p R o)(f:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(j:Ovens.Label)(U:Config G n):Polynomial (Poly R):=
  Polynomial.C (S.ink j U)+Polynomial.C (dye X f h j U)*Polynomial.X

private theorem modes (S:(layout X).Stock p R o)(f:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(j:Ovens.Label)(U:Config G n):
    (letters S f h j U).coeff 0=S.ink j U ∧ (letters S f h j U).coeff 1=dye X f h j U:=by
  simp [letters]

theorem coefficient {ι:Type*}[DecidableEq ι](L:Finset ι)(f:ι → Polynomial (Poly R)):
    (∏i∈L,f i).coeff 1=∑i∈L,(∏j∈L.erase i,(f j).coeff 0)*(f i).coeff 1:=by
  have id:=congrArg (fun z:Polynomial (Poly R) => z.coeff 0) (Polynomial.derivative_prod_finset (s:=L) (f:=f))
  simpa [Polynomial.coeff_derivative,Polynomial.mul_coeff_zero,Polynomial.coeff_zero_prod,Polynomial.finsetSum_coeff] using id

theorem traced (e:ℕ≃X.Pellet)(S:(layout X).Stock p R o)(f:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(k:ℕ)(U:Config G n):
    let K:=receipt e p (letters S f h) k U
    K.coeff 0=Attached.marked e S k U ∧
    K.coeff 1=if (addr e p k).eligible p.threshold U then
      ∑i∈(e k).val,(∏j∈(e k).val.erase i,S.ink j U)*dye X f h i U else 0:=by
  intro K
  refine ⟨constant e S _ (fun i u => (modes S f h i u).1) k U,?_⟩
  dsimp only [K,receipt]
  split
  · rw [coefficient]
    simp only [(modes S f h _ U).1,(modes S f h _ U).2]
  · simp

theorem location (e:ℕ≃X.Pellet)(p:BudgetPoint)(k:ℕ)(head hard:Ovens.Label)
    (a:head∈(e k).val)(b:hard∈(e k).val)(x:Site n)(inside:x∈X.patch head):
    x∈(addr e p k).support ∧ Ac.chain X.patch (e k).val head hard:=by
  constructor
  · rw [←support_eq e k]
    exact Finset.mem_biUnion.mpr ⟨head,a,inside⟩
  · exact (e k).property.2.1.2 head a hard b

private theorem pricedSum {ι:Type*}(w:V → ℝ)(hw:∀v,0<w v)(L:Finset ι)(f:ι → Poly R):
    Poly.price w (∑i∈L,f i) ≤ ∑i∈L,Poly.price w (f i):=by
  induction L using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (Poly.addition hw ..).trans (add_le_add le_rfl ih)

theorem rooted (e:ℕ≃X.Pellet)(S:(layout X).Stock p R o)(w:V → ℝ)(hw:∀i,0<w i)
    {ρ:ℝ}(hr:0<ρ)(f:ℕ → Site n → Config G n → Poly R)(base:Ovens.Label → ℝ)(extra:ℕ → ℝ)
    (base0:∀i,0 ≤ base i)(extra0:∀i,0 ≤ extra i)
    (ob:∀i U,Poly.price w (S.ink i U) ≤ base i)
    (obx:∀i U,(∑x∈(X.kernel i).support,Poly.price w (f i x U)) ≤ extra i)
    {a χ γ:ℝ}(ha:0 ≤ a)(hx:1 ≤ χ)(hg:0 ≤ γ)
    (fund:Hit X.patch p.B (fun j => Sum.elim (fun _ => χ) (fun _ => 1) j*(base j+ρ*j.elim extra (fun _ => 0))) (a+1) γ)
    (room:(p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1)(head:Ovens.Label)(anchor:Site n)(own:anchor∈X.patch head):
    let cap (j:Ovens.Label):=base j+ρ*j.elim extra (fun _ => 0)
    let bill (i:ℕ):=if head∈(e i).val then income e cap i/ρ else 0
    SumBudget (fun i => bill i*Real.exp (a*coverNumber p.B (addr e p i).support)) (((Real.exp γ-1)/χ)/ρ) ∧
    ∀(h:Site n → ℂ), (∀x,‖h x‖ ≤ 1) → ∀k U,head∈(e k).val →
      Poly.price w ((receipt e p (letters S f h) k U).coeff 1) ≤ bill k:=by
  intro cap bill
  have pos(j:Ovens.Label):0 ≤ cap j:=by
    cases j with
    | inl i => exact add_nonneg (base0 _) (mul_nonneg hr.le (extra0 i))
    | inr i => simpa [cap] using base0 (Sum.inr i)
  have finance:=pension R e p hw cap pos ha hx hg fund room
  have inc(i:ℕ):0 ≤ income e cap i:=Finset.prod_nonneg fun j _ => pos j
  constructor
  · have scalar:=budget_scale (inv_nonneg.mpr hr.le) (finance anchor)
    rw [div_eq_inv_mul]
    apply budget_mono scalar
    · intro i
      dsimp only [bill]
      split <;> positivity [inc i]
    · intro i
      by_cases contact:head∈(e i).val
      · have fits:anchor∈(addr e p i).support:=(location e p i head head contact contact anchor own).1
        simp only [bill,contact,fits,if_true,div_eq_inv_mul];ring_nf;exact le_rfl
      · simp only [bill,contact,if_false,zero_mul]
        split <;> positivity [inc i]
  · intro h hh
    have coverage(i:Ovens.Label)(U:Config G n):salary w ρ (letters S f h i U) ≤ cap i:=by
      dsimp only [salary,cap]
      rw [(modes S f h i U).1,(modes S f h i U).2]
      apply add_le_add (ob i U) (mul_le_mul_of_nonneg_left _ hr.le)
      cases i with
      | inr j => simp [dye]
      | inl j =>
        apply (pricedSum w hw _ _).trans
        refine (Finset.sum_le_sum fun x _ => ?_).trans (obx j U)
        rw [Poly.adapted]
        exact mul_le_of_le_one_left (Poly.nonnegative hw _) (hh x)
    intro k U inside
    simpa only [bill,inside,if_true] using (paid e p hw hr (letters S f h) cap pos coverage ha hx hg fund room).2.2 k U
end YM.Integration.WilsonRootedFusionFirstJoin
