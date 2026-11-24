import YM.Integration.WilsonNeutralTwoPrintPathRankFare
import YM.Integration.WilsonOriginalRelativePageIncome
import YM.Integration.WilsonPointChildDeckAngular
import YM.Integration.WilsonPointChildRelativeLift

/-! Absolute angular invoices for the genuine separate copies of an occupied family,
on a single enlarged lattice, after fixing one copy of its root. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPageLedger
open Function Finset Lattice Laurent Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained locate)
open WilsonPointChildRelativeLift (centers)
open WilsonPointChildDeckAngular (window)
open UVNext.PricedKernels
open scoped BigOperators Classical
open private spent from YM.Integration.WilsonNeutralTwoPrintPathRankFare
variable {V α ι:Type} [NormedAddCommGroup V][NormedSpace ℝ V][Fintype α]{n X:Side}{r:ℕ}

theorem individual (J:Finset ι)(p:ι→Site X)(a:ι)(live:a∈J)(σ A:ℝ)(hs:0<σ)
    (K:Ten V (Site X × α) r)(test:V →L[ℝ] ℂ)(gross:Wig (tor X) p σ A J K):
    ∑x,Real.exp ((σ/2)*(Syn (tor X) p J x:ℝ))*‖test (K x)‖ ≤ 
      (‖test‖*A)*tiePay α r (σ/2):=by
  let H:Ten ℂ (Site X × α) r:=fun x=>(Real.exp ((σ/2)*(Syn (tor X) p J x:ℝ)):ℂ)*test (K x)
  have W:Wig (tor X) p (σ/2) (‖test‖*A) J H:=by
    refine ⟨mul_nonneg (norm_nonneg _) gross.1,?_⟩
    intro x
    simp only [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp ((σ/2)*(Syn (tor X) p J x:ℝ))*(‖test‖*
          (A*Real.exp (-σ*(Syn (tor X) p J x:ℝ)))):=
        mul_le_mul_of_nonneg_left ((test.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (gross.2 x) (norm_nonneg _))) (Real.exp_pos _).le
      _ = _:=by
        rw [show -(σ/2)*(Syn (tor X) p J x:ℝ)=(σ/2)*(Syn (tor X) p J x:ℝ)+ -σ*(Syn (tor X) p J x:ℝ) by ring,
          Real.exp_add]
        ring
  simpa only [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    (spent ⟨a,live⟩ (by positivity:0<σ/2) W)

open private tail from YM.Integration.WilsonPointChildDeckAngular

private theorem housing {a Z:Type} [dec:DecidableEq a][Fintype a][Fintype Z]
    (h:n.val∣X.val)(root:Site X)(site:a→Site X)
    (K:(a→Fin (Pages n X))→Z→ℂ)(span:(a→Fin (Pages n X))→Z→ℝ)
    {ρ A:ℝ}(strip:0<ρ)(fee:0 ≤ A)(length:∀p x,0 ≤ span p x)
    (reach:∀p x i,(separation root (locate h site p i):ℝ) ≤ span p x)
    (one:∀p,(∑x,Real.exp (ρ*span p x)*‖K p x‖) ≤ A):
    (∑p,∑x,Real.exp (ρ/2*span p x)*‖K p x‖) ≤ A*(basin (ρ/(2*(Fintype.card a+1:ℝ))))^Fintype.card a:=by
  obtain rfl:dec=fun a b=>Classical.propDecidable (a=b):=Subsingleton.elim _ _
  exact WilsonOriginalRelativePageIncome.original h root site K span strip fee length reach one

variable [DecidableEq ι]
def price (J:Finset ι)(a:ι)(α:Type)[Fintype α](r:ℕ)(σ A:ℝ):ℝ:=
  (A*tiePay α r (σ/2))*(basin ((σ/2)/(2*(Fintype.card (J.erase a)+1:ℝ))))^Fintype.card (J.erase a)

theorem original (h:n.val∣X.val)(J:Finset ι)(a:ι)(live:a∈J)(root:Site X)
    (site:(J.erase a)→Site X)(D:ℝ)(near:∀v,(separation root (site v):ℝ) ≤ D)
    (σ A:ℝ)(hs:0<σ)(test:V →L[ℝ] ℂ)
    (K:((J.erase a)→Fin (Pages n X))→Ten V (Site X × α) r)
    (gross:∀p,Wig (tor X) (wrap X ∘ toe J a (lift root) (centers h J a root site p)) σ A J (K p)):
    let span:=fun p (x:dock (Site X) α r)=>(Syn (tor X) (wrap X ∘ toe J a (lift root) (centers h J a root site p)) J x:ℝ)
    let C:=price J a α r σ (‖test‖*A)
    (∑p,∑x,Real.exp ((σ/2)/2*span p x)*‖test (K p x)‖) ≤ C ∧
      (∑x,Real.exp (((σ/2)/2)*window root x/2)*
        ‖(∑p,test (K p x))-test (K (retained h site) x)‖) ≤ 
        Real.exp (-(((σ/2)/2)*((n.val:ℝ)-D))/2)*C:=by
  intro span C
  let row:=fun p x=>test (K p x)
  have reaches:∀p x i,(separation root (locate h site p i):ℝ) ≤ span p x:=
    fun p x i=>Nat.cast_le.mpr (WilsonPointChildRelativeLift.connected h J a live root site r p x i)
  have home (p:(J.erase a)→Fin (Pages n X)):wrap X (toe J a (lift root) (centers h J a root site p) a)=root:=by simp [toe]
  have inside:∀p x,window root x ≤ span p x + 0:=by
    intro p x
    rw [add_zero]
    exact WilsonPointChildDeckAngular.included J a live root _ (home p) r x
  have one p:=individual J _ a live σ A hs (K p) test (gross p)
  have earned:0 ≤ (‖test‖*A)*tiePay α r (σ/2):=
    (sum_nonneg (fun _ _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).trans (one (retained h site))
  have joint:=housing h root site row span (by positivity:0<σ/2)
    earned (by intro p x;exact Nat.cast_nonneg _) reaches one
  refine ⟨joint,?_⟩
  exact tail h root site row span (window root) (show 0 ≤ σ/2/2 by positivity) near reaches
    (fun p x=>by simpa only [add_zero] using inside p x) joint

end YM.Integration.WilsonNeutralTwoPrintPathPageLedger
end
