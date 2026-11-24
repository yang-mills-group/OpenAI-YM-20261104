import YM.RG05Readout.Nuclear.Kite
import Mathlib.LinearAlgebra.Vandermonde
/-! NIB -- summation-by-parts stencil existence for *all* needed jets
in these same threshold letters. Uses only backward evaluation on integer grid.
Polynomial reproduction total multi jet not treating screened offsets or
periods yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Nuclear Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "J"=> Complexion E
-- argument in ray. real interpolation sends values at real nodes (roots) to all
abbrev Slots (k:ℕ):= Axis→Fin (k+1)
def backward {k:ℕ}(s : Slots k) : Cover := fun j=> s j
noncomputable def away (v:Cover):E4:= WithLp.toLp 2 fun i=> -((v i:ℤ):ℝ)
noncomputable def chair (n:ℕ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]:Submodule ℂ (Complexion E) where
    carrier := {p|iteratedFDeriv ℝ (n+1) p.val=0}
    zero_mem' := by change iteratedFDeriv ℝ _ (0:E→ℂ)=0; simp
    add_mem' := by
       intro u v hu hv; change iteratedFDeriv ℝ (n+1) _ = 0; rw [AddMemClass.coe_add,iteratedFDeriv_add (lit u _) (lit v _),show iteratedFDeriv ℝ _ u.val=0 from hu,show iteratedFDeriv ℝ _ v.val=0 from hv,add_zero] -- simp
    smul_mem' := by
       intro c u hu; change iteratedFDeriv ℝ _ (_ • u.val)=0; funext x; rw [iteratedFDeriv_const_smul_apply (lit u _|>.contDiffAt), show iteratedFDeriv ℝ _ u.val=0 from hu]; exact smul_zero _
lemma line_stamp (x u:E)(p:Complexion E)(hp:p∈chair d E) : ∃ w:Fin (d+1)→ℂ,∀ t:ℝ,p.val (x+t • u) = ∑ i: Fin (d+1), (t^i.val) • w i:=by
    let P:= fork 1 x p; let c(i:ℕ):= Tensor.coeff P.val i 0; let a(v:Fin (d+1)):= Tensor.diagonal (c v.val) u
    refine ⟨a,fun t=>?_⟩; have he:= abroad x p (show iteratedFDeriv ℝ (d+1) _=0 from hp); apply (congr_fun (congr_arg Subtype.val he) (x+t • u)).trans
    change Work.G05.blockTaylor d P.val (-x + 1 • (x+t • u))=_; rw [one_smul, neg_add_cancel_left]; change (∑ i∈Finset.range (d+1), Tensor.diagonal (c i)) _=_;rw [Finset.sum_apply,← Fin.sum_univ_eq_sum_range (fun i=>Tensor.diagonal (c i) (t • u))]; refine Finset.sum_congr rfl (fun i _=>?_)
    unfold Tensor.diagonal; rw [(c i.val).map_smul_univ (fun _=>t) (fun _=>u)]; simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl
lemma through (x v:E)(p:J)(hp:p∈chair k E)(hh:∀ i: Fin (k+1), p.val (x+ (↑(i.val):ℝ) • v)=0): ∀ t:ℝ,p.val (x+t • v)=0:=by
    obtain ⟨a,hA⟩:=line_stamp x v p hp; let M:= Matrix.vandermonde (fun i: Fin (k+1)=> (i.val:ℂ)); have hg:IsUnit M.det:=by rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]; intro i j he; apply Fin.ext; exact_mod_cast (show (i.val:ℂ)=(j.val:ℂ) from he)
    have he:(M.mulVec a)=0:=by funext i; rw [Pi.zero_apply,← show p.val _=_ from hh i, hA]; unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_ ; unfold M; simp only [Matrix.vandermonde, Matrix.of_apply, Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_natCast]
    have hv:a=0:=by rw [← Matrix.one_mulVec a,← Matrix.nonsing_inv_mul M hg,← Matrix.mulVec_mulVec,he,Matrix.mulVec_zero]
    intro t; rw [hA,hv]; simp
local notation "W"=> chair d E4
lemma grid_dict (φ:Body)(ht:φ∈ chair k E4)(h:∀ i:Slots k, φ.val (away (backward i))=0) (z:E4): φ.val z=0:=by
   let P:=fun s:Finset Axis=> ∀ z:E4,∀ w:Slots k, (∀ i:Axis, i∉s → z i= -(↑(w i).val:ℝ)) → φ.val z=0
   suffices he:∀ s,P s from he Finset.univ z 0 (by simp)
   intro s; induction s using Finset.induction_on with
   | empty=>
       intro a w hv; have he:a=away (backward w):= by
                            ext i; change a i= - (↑((w i).val:ℤ):ℝ); rw [Int.cast_natCast]; exact hv i (by simp)
       exact he ▸ h w
   | insert i s hi ih=>
      intro a w hz; let x:= a - a i • basis i
      have hw(j: Axis)(b:ℝ)(h:j≠i) : (x+b • (-basis i)) j= a j:= by unfold x; rw [PiLp.add_apply, PiLp.sub_apply,PiLp.smul_apply,PiLp.smul_apply];simp [h]
      have he :∀ j:Fin (k+1), φ.val (x + (↑j.val:ℝ) • (-basis i))=0:=by
          intro j; apply ih _ (Function.update w i j); intro l hh; by_cases hg:l=i
          · subst l; unfold x; rw [Function.update_self,PiLp.add_apply, PiLp.sub_apply,PiLp.smul_apply,PiLp.smul_apply]; simp
          rw [hw _ _ hg,hz l (by simp [hh,hg]),Function.update_of_ne hg]
      exact (show x+ (-a i) • (-basis i)=a by unfold x; rw [neg_smul,smul_neg,neg_neg,sub_add_cancel]) ▸ through x (-basis i) φ ht he (-a i)
noncomputable def spent (a:Slots d): chair d E4→ₗ[ℂ]ℂ where
   toFun f:= f.val.val (away (backward a))
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
local notation "B"=> chair d E4
private lemma fitting {I X:Type}[Fintype I][AddCommGroup X][Module ℂ X](a:I→X→ₗ[ℂ]ℂ)(T:X→ₗ[ℂ]ℂ)(ht:∀ v:X,(∀ i,a i v=0)→ v=0):∃ c:I→ℂ,∀ x,T x=∑ i,c i*a i x:=by
     let w:=LinearMap.pi a; have hp:Injective w:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x h=> ht x (fun i=>congr_fun h i)))
     letI : FiniteDimensional ℂ X:= Module.Finite.of_injective w hp; have hv: ⨅ i, LinearMap.ker (a i) ≤ LinearMap.ker T:= by
       intro x hx; rw [ht _ (fun i=> LinearMap.mem_ker.mp ((Submodule.mem_iInf _).1 hx i))]; exact Submodule.zero_mem ..
     have he:T∈Submodule.span ℂ (Set.range a):=FiniteDimensional.mem_span_of_iInf_ker_le_ker hv
     obtain ⟨c,hc⟩:=Finsupp.mem_span_range_iff_exists_finsupp.mp he; refine ⟨c,fun p=>?_⟩; rw [←hc]; unfold Finsupp.sum; rw [LinearMap.sum_apply]; apply Finset.sum_subset (f:=fun i=> c i * a i p) (Finset.subset_univ _); simp only [Finsupp.mem_support_iff, not_not]; intro i _ hx; rw [hx,zero_mul]
lemma swatches (d:ℕ)(k:Letter n) : ∃ c:Slots d→ℂ, ∀ p:Body,p ∈ chair d E4 → readJ k 0 p =∑ i:Slots d, c i* p.val (away (backward i)) :=by
   let f(i:Slots d):= spent i; let T : (chair d E4)→ₗ[ℂ]ℂ:= readJ k 0 ∘ₗ (chair d E4).subtype
   have ht(x:chair d E4)(hx:∀ i:Slots d,f i x=0):x=0:=by apply Subtype.ext; apply Subtype.ext; exact funext fun y=> grid_dict x.val x.property hx y
   obtain ⟨c,hc⟩:= @fitting (Slots d) (chair d E4) _ _ _ f T ht; exact ⟨c,fun p h=>hc (⟨p,h⟩:(chair d E4))⟩
noncomputable def weights (d:ℕ)(k:Letter n): Slots d→ℂ:= (swatches d k).choose
lemma postal (d:ℕ)(k:Letter n)(p:Body)(h:p∈chair d E4) : readJ k 0 p= ∑ i:Slots d, weights d k i* p.val (away (backward i)):= (swatches d k).choose_spec p h
end YM.RG05Readout.Petals
