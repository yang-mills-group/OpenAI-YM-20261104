import YM.Integration.WilsonSubcriticalMSConnected

/-! The full ordered MS moment of constant insertions. Every disconnected singleton
is retained on its original normalization, so this applies also to odd arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalMSMoments
open Function Set Filter Finset MeasureTheory MS MS.Plane MS.Arts MS.Land MS.Motif MS.Local.Physical MS.Rake MS.Rake.Geo
open MS.Dial MS.Tone MS.Vane MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Menus
open WilsonSubcriticalRichOptics WilsonSubcriticalMSConnected
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} {A:Booked B} {W:Type} [LinearOrder W]

def constant (z:ℂ):T ℂ:=fun k=>if k=0 then z else 0

private theorem convolution (a b:ℂ):Trunk.core (constant a) (constant b)=constant (a*b):=by
  funext k;change (∑v∈antidiagonal k,constant a v.1*constant b v.2)=constant (a*b) k
  by_cases h:k=0
  · subst k;simp [constant]
  rw [constant,if_neg h];apply sum_eq_zero
  intro v hv;have e:=mem_antidiagonal.mp hv
  by_cases i:v.1=0
  · have j:v.2≠0:=by omega
    simp [constant,j]
  · simp [constant,i]

theorem products (z:W→ℂ)(s:Finset W):bouquet (WilsonSubcriticalMSConnected.amount z) s=constant (∏w∈s,z w):=by
  have empty:WilsonSubcriticalMSConnected.amount z (∅:Finset W)=0:=by funext k;simp [WilsonSubcriticalMSConnected.amount]
  have guard:∀s,WilsonSubcriticalMSConnected.amount z s∈Trunk.guard:=fun _=>(universe0 _).mpr fun _=>Submodule.mem_top
  have single:∀t:Finset W,t.card≠1→WilsonSubcriticalMSConnected.amount z t=0:=by intro t i;funext k;simp [WilsonSubcriticalMSConnected.amount,i]
  induction s using Finset.induction_on with
  | empty=>
    have e:=Stencil.simple_E Trunk (WilsonSubcriticalMSConnected.amount z) (marked W) empty
    change Cheer Trunk (marked W) (WilsonSubcriticalMSConnected.amount z) (marked W).origin=_
    rw [e,Finset.prod_empty];funext k;change SplitP.refineV SplitP.nat (1:ℂ) k=constant 1 k;unfold SplitP.refineV constant
    by_cases zero:k=0
    · subst k;rw [if_pos (show (0:ℕ)=SplitP.nat.origin from rfl),if_pos rfl]
    · rw [if_neg (show k≠SplitP.nat.origin from zero),if_neg zero]
  | insert w s h ih=>
    change Cheer Trunk (marked W) (WilsonSubcriticalMSConnected.amount z) (insert w s)=_
    rw [Stencil.cheers Trunk guard single s w h,←show bouquet (WilsonSubcriticalMSConnected.amount z) s=Cheer Trunk (marked W) (WilsonSubcriticalMSConnected.amount z) s from rfl,ih]
    have base:WilsonSubcriticalMSConnected.amount z {w}=constant (z w):=by funext k;simp [WilsonSubcriticalMSConnected.amount,constant]
    rw [base,convolution,Finset.prod_insert h]

theorem whole (M:MS_Data G A)(j:W→Plaid B 0)(u:ℝ){x:W→QP}(sep:Injective x)(s:Finset W):
    Dial.tour M (fun w=>⟨0,j w⟩) u x s=constant (∏ w∈s,valueAtUnit (j w)):=by
  change bouquet (Dial.book M (fun w=>⟨0,j w⟩) u x) s=_
  rw [show Dial.book M (fun w=>⟨0,j w⟩) u x=WilsonSubcriticalMSConnected.amount (fun w=>valueAtUnit (j w)) from funext fun c=>funext fun k=>WilsonSubcriticalMSConnected.book M j u sep c k]
  exact products _ _

end YM.Integration.WilsonSubcriticalMSMoments
