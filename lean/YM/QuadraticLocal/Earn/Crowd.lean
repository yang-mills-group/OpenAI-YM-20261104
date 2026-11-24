import YM.QuadraticLocal.Earn.Club
import YM.RemainderComparison.Breeze.Baskets
/-! # Cumulative costs of ALL possible outgoing rooted interactions

 Use exponential kernel economy, radius exposures separate from pure holder. Never infer lack of
 mixed-multiple ROOT loads from their packing. Old footprints travel; linearity factor `b` in
 addition to announced all-slot weight dollars. Especially, one stencil can have infinitely many
 calls in a bounded small ball in *this period*, e.g. spending small funds of the non-model
 wrappers. There is no constraint on occupancy from merely announcing V.

 Need Width to use these bills on EVERY root and derivative: they are only for the projection
 economic step. Earnings polynomial in geometry for the `inside` cost; exposures compute later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn.Club RemainderComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ} {k u i' j h : ℕ}
variable (X:ι→ Row P R G α) (q:Ratio c n) (w:V→ℝ) (hw:∀ i,0<w i)
namespace Accumulate
local notation "C"=> (Club X)
set_option quotPrecheck false
-- expose each normalized magnitude exactly

def rootPrice (a:ℝ)(F:C) := ∏ i ∈ F.val, Poly.toll w (X i).mode*(X i).height a
local notation "φ"=> rootPrice X w σ
variable (F:Club X)
include hw
lemma pieces (a:ℝ)(i:ι) : 0<Poly.toll w (X i).mode*(X i).height a:= mul_pos (Poly.worth hw _) (mul_pos (X i).sound (Real.exp_pos _))
lemma active (σ:ℝ): 0<rootPrice X w σ F:= Finset.prod_pos fun i _=> pieces X w hw σ i
local notation "L"=> q.count.val
local notation "u₀"=> (fun i:ι=> (X i).center)
local notation "p₀"=> (fun i:ι=> q.parent ((X i).center))
local notation "Lx" => ((q.count.val:ℝ)^4)
local notation "w₀"=> (fun i:ι=> Poly.toll w (X i).mode * (X i).height σ)
variable (hp:Offers X w σ b)
include hp
lemma projected (v:Site c) : SumBudget (fun i:ι=> if mask X q i=v then w₀ i else 0) (Lx*b):=by
    let S:=univ.filter fun i:Site n=>q.parent i=v; have hV : S.card≤ L^4:= by simpa only [Finset.card_singleton,one_mul,mem_singleton] using Footprint.crowd q ({v}: Support c)
    have hb:0 ≤ b:= budget_nonneg (hp 0)
    let f i:= if mask X q i=v then w₀ i else 0
    have he(x:ι) : f x≤ ∑ i∈S, if u₀ x = i then w₀ x else 0 := by
       unfold f; split; next h=>
          refine le_trans (b:= if u₀ x=u₀ x then w₀ x else 0) (by simp) (Finset.single_le_sum (s:=S) (f:=fun i=> if u₀ x=i then w₀ x else 0) (fun i _=> (hp i).1 x) (show u₀ x∈ S from mem_filter.mpr ⟨mem_univ _,h⟩))
       next=> exact Finset.sum_nonneg (fun i _=> (hp i).1 x)
    exact budget_loosen (budget_mono (budget_over S _ _ (fun i _=> hp i)) (fun i=> by split; exact (pieces X w hw ..).le; rfl) he) (by simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hV) hb)

variable (hb: b≤1) (hk:∀ t: Club X,t.val.card ≤ k)
local notation "λ!"=> Club.reach X
local notation "Y"=> fun h=> Club.roof X h q
local notation "ψ"=> fun h=> Club.reach X h q
local notation "σA" => (fun C₁=> Club.alliance X C₁)
def closer (F:C)(v:Site c)(i:ℕ):Prop:= reach X F q ≤ i ∧ roof X F q=v
local notation "A₁" i:max=> Breeze.areaBudget i k Lx
variable (k)
include hb hk
-- area prices WITHOUT β.E.Ph.Style.Operation.Body
lemma inside (i:ℕ)(v:Site c) : SumBudget (fun F:Club X=> if closer X q F v i then rootPrice X w σ F else 0) (b* A₁ i):=by
    by_cases h:0<b; swap;
    · have hz: b=0:= le_antisymm (not_lt.mp h) (budget_nonneg (hp 0)); subst b; rw [zero_mul];
      haveI : IsEmpty ι:= ⟨fun I=> (pieces X w hw σ I).not_ge (le_trans (b:=if u₀ I = (X I).center then w₀ I else 0) (by simp) (budget_single (hp ((X I).center)) I))⟩
      haveI : IsEmpty (Club X):= ⟨fun I=> by obtain ⟨j,h⟩:= I.prop.1; exact isEmptyElim j⟩
      exact budget_of_sum (fun i=>isEmptyElim i) (fun I=> by rw [Finset.eq_empty_of_isEmpty I,sum_empty])
    let S := {F:Club X// closer X q F v i}; let P: Breeze.Careers ι S c (mask X q) i k := ⟨⟨(fun F=> F.val.val), Subtype.val_injective.comp Subtype.val_injective⟩, (fun _=>v), fun z j hj=> (by
       obtain ⟨ht,h⟩:=z.prop; rw [← h]; exact (brings X z.val q _ hj).trans ht), (fun j=>hk j.val)⟩; -- Prop inf
    let g i:=(w₀ i)/b; have hg i:0≤g i:= (div_pos (pieces X w hw ..) h).le
    have he(x) : SumBudget (fun i=>if mask X q i=x then g i else 0) Lx:=by
       convert budget_scale (inv_pos.mpr h).le (projected X q w hw hp x) using 1
       · ext i; split; exact div_eq_inv_mul ..; exact (mul_zero _).symm
       field_simp
    let hf (F:Club X):= closer X q F v i; let f F:= if hf F then rootPrice X w σ F else 0
    have hA:= budget_scale h.le (Breeze.ribbons _ _ P hg he v)
    have hz : SumBudget f (b*A₁ i) := by
       refine Progress.DirectedRecipe.transfer_budget (t:= (show S ↪ Club X from ⟨Subtype.val, Subtype.val_injective⟩)) (f:=f) (fun (I:S)=> rfl) (fun I he=> ?_) (budget_mono (g:=fun (u:S)=>f u.val) hA ?_ ?_)
       · unfold f; rw [if_neg]; exact fun h=>he ⟨⟨I,h⟩,rfl⟩
       · intro i; unfold f; rw [if_pos i.prop]; exact (active X w hw ..).le
       · intro z; let s:=z.val.val; let v':=∏ j∈s,g j; have ht':f z.val=b^s.card*v':=by
             unfold f; rw [if_pos z.prop]; change (∏ i∈s,w₀ i)= _; unfold v' g; rw [Finset.prod_div_distrib,Finset.prod_const]; field_simp
         rw [ht',if_pos (show P.o' z=v from rfl)]; apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg («f»:=g) (fun i _=> hg i)); nth_rw 2 [← pow_one b]; exact pow_le_pow_of_le_one h.le hb (Finset.card_pos.mpr z.val.prop.1)
    exact hz

end Accumulate
end YM.QuadraticLocal.Earn
