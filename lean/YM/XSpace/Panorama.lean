import YM.XSpace.Aisles
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Parametrized finite response and smooth near-identity frame solve

To make the mathematics work at **finite mesh** don't assume order-zero arrays hit
position data exactly. Use IFT with parameters taking finitely many test readings,
even during arity/moduli unrestricted expansions. Real coordinates to use Space topology.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n l:ℕ}
abbrev Pin (G:Gauge) (d:ℕ):= Fin (Module.finrank ℝ (Sec G d))
abbrev MoveSpace (G:Gauge) (d:ℕ):= Fin (Module.finrank ℝ (Change G d))→ℝ
def guide (G:Gauge) (d:ℕ): (Change G d)≃ₗ[ℝ] MoveSpace G d:= (Module.finBasis ℝ (Change G d)).equivFun
lemma medium (p:Fin n→ Sec G d) (Q:MultilinearMap ℝ (fun _ : Fin n=> Sec G d) ℂ): Q p=∑ r : Fin n→ Pin G d,(∏ i, tableD G d (p i) (r i)) • Q (fun i=> Module.finBasis ℝ (Sec G d) (r i)):=by
  let A:=Module.finBasis ℝ (Sec G d)
  have he:= Q.map_sum (fun i (j:Pin G d)=> A.repr (p i) j • A j)
  rw [show Q p=∑ r: Fin n→Pin G d,Q (fun i=>A.repr (p i) (r i) • A (r i)) by simpa only [A.sum_repr] using he]; exact Finset.sum_congr rfl fun i _=> Q.map_smul_univ _ _
lemma closed_move (P:Prediction G d) (w:Window G d) (v:MoveSpace G d) (K:Change G d) :
    HasDerivAt (fun t:ℝ=> watch w (recruit (stand ((guide G d).symm (v+t • guide G d K))) P)) (watch w (tang (stand ((guide G d).symm v)) K.val P)) 0:=by
  let x:= (guide G d).symm v; let f (s:ℝ) (i:Fin w.n):= stand (x+s • K) (w.p i); let y i:= K.val (w.p i); let u:= tableD G d; let A:= ((P w.n w.t).restrictScalars ℝ).compLinearMap fun i:Fin w.n=> u.symm.toLinearMap; let L : ContinuousMultilinearMap ℝ (fun _:Fin w.n=>RSpace G d) ℂ:= ⟨A,cont_land A⟩
  have h (g:Fin w.n→ Sec G d): L (u ∘ g)=P w.n w.t g:=by change P _ _ (fun i=> u.symm (u (g i)))=_; simp
  have he i : HasDerivAt (fun s=> u (f s i)) (u (y i)) 0 := by
    have hh (s:ℝ): u (f s i)= u (stand x (w.p i))+ s • u (y i):=by
      unfold f; simp_rw [stood, Submodule.coe_add, Submodule.coe_smul_of_tower,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]; unfold y; abel
    simp_rw [hh]; simpa only [one_smul,zero_add] using! ((hasDerivAt_const (0:ℝ) (u (stand x (w.p i)))).add ((hasDerivAt_id' (0:ℝ)).smul_const (u (y i))))
  have hg: HasDerivAt (L ∘ (fun s=> u ∘ f s)) (∑ i,P w.n w.t (update (stand x ∘ w.p) i (y i))) 0 := by
    apply HasDerivAt.congr_deriv ((L.hasFDerivAt (u ∘ f 0)).comp_hasDerivAt (0:ℝ) (show HasDerivAt (fun s=> u ∘ f s) (u ∘ y) 0 from hasDerivAt_pi.mpr (fun i=> he i))); rw [ContinuousMultilinearMap.linearDeriv_apply]; apply Finset.sum_congr rfl; intro i _; rw [← h]; congr 1; funext j; by_cases hj:j=i <;> simp [f,hj,Function.comp_apply]
  change HasDerivAt (fun t:ℝ=> P _ w.t (stand ((guide G d).symm _) ∘ w.p)) (tang _ _ P w.n w.t w.p) 0
  simp_rw [touches,map_add,map_smul,LinearEquiv.symm_apply_apply]; rw [show L ∘ (fun s=> u ∘ f s)=(fun s=> P _ w.t (f s)) from funext fun s=> h (f s)] at hg; exact hg

structure Fray (A:Screen G d) where
  n:ℕ
  scope : Fin n→Window G d
  tally : (Fin n→ℂ)→ₗ[ℝ] Change G d
  equal : ∀ U: Prediction G d,tally (fun i=> watch (scope i) U)=A.D U
lemma choose_fray (A:Screen G d): Nonempty (Fray A):=by obtain ⟨n,v,P,h⟩:= A.observable; exact ⟨n,v,P,fun _=>(h _).symm⟩
namespace Fray
variable {A:Screen G d} (D:Fray A)
abbrev Bag := (i:Fin D.n)→ (Fin (D.scope i).n→ Pin G d)→ℂ

def purse (P : Prediction G d): D.Bag:= fun i r=> P (D.scope i).n (D.scope i).t (fun j=> Module.finBasis ℝ (Sec G d) (r j))
def box (u:MoveSpace G d):= stand ((guide G d).symm u)
def stamps : (Fin D.n→ℂ)→L[ℝ] MoveSpace G d:= LinearMap.toContinuousLinearMap ((guide G d).toLinearMap ∘ₗ D.tally)
def itinerary (v:D.Bag × MoveSpace G d) := D.stamps fun i=> ∑ r:Fin (D.scope i).n→Pin G d,(∏ j, tableD G d (box v.2 ((D.scope i).p j)) (r j)) • v.1 i r
lemma way (P:Prediction G d) (v: MoveSpace G d): D.itinerary (D.purse P,v)= guide G d (A.D (recruit (box v) P)):=by
  rw [← D.equal]; change D.stamps _ = D.stamps _; apply congr_arg; ext1 i; exact Eq.symm (medium _ ((P (D.scope i).n (D.scope i).t).restrictScalars ℝ))

private def ways (p:Sec G d): MoveSpace G d→L[ℝ] RSpace G d:= LinearMap.toContinuousLinearMap { toFun v:= tableD G d (((guide G d).symm v).val p), map_add' := by intro a b; rw [map_add]; exact map_add (tableD G d) _ _, map_smul':=by intro a b; rw [map_smul]; exact map_smul (tableD G d) _ _ }
lemma fair : ContDiff ℝ ω D.itinerary:=by
  apply ContDiff.comp D.stamps.contDiff; apply contDiff_pi.mpr; intro i; apply ContDiff.sum; intro r _; apply ContDiff.smul (f:= fun v: D.Bag × MoveSpace G d=>∏ j,tableD G d (box v.2 ((D.scope i).p j)) (r j)) (g:=fun v=> v.1 i r); swap
  · exact contDiff_pi.mp (contDiff_pi.mp contDiff_fst i) r
  apply contDiff_prod; intro j _; let p:= (D.scope i).p j; change ContDiff ℝ ω (fun u: D.Bag × MoveSpace G d=> (tableD G d (box u.2 p)) (r j)); simp_rw [box,stood,map_add]; exact (contDiff_apply ℝ ℝ (r j)).comp (contDiff_const.add ((ways p).contDiff.comp contDiff_snd))

abbrev At := D.Bag × MoveSpace G d
def opening : D.At:= (D.purse (reference G d),0)
def align (p:MoveSpace G d) (P:Prediction G d) := slope A ((guide G d).symm p) P

def delta (x:D.At): MoveSpace G d→L[ℝ] MoveSpace G d:= fderiv ℝ D.itinerary x ∘L ContinuousLinearMap.inr ℝ D.Bag _
lemma order (P:Prediction G d) (v: MoveSpace G d) (X:Change G d): D.delta (D.purse P,v) (guide G d X) = guide G d (align (A:=A) v P X):= by
  let u:=guide G d; let a (t:ℝ):= v+t • u X
  let f (t:ℝ):= (D.purse P, a t); have hf : HasDerivAt f (0,u X) 0 := by simpa [f,a] using! ((hasDerivAt_const (0:ℝ) (D.purse P)).prodMk ((hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id' (0:ℝ)).smul_const _)))
  have hh := D.fair.differentiable (by simp); have hx:f 0=(D.purse P,v):=by simp [f,a]
  change fderiv ℝ D.itinerary (D.purse P,v) (0,u X)=_
  rw [← hx]; apply HasDerivAt.unique ((hh _ |>.hasFDerivAt).comp_hasDerivAt (0:ℝ) hf)
  have he : D.itinerary ∘ f=D.stamps ∘ (fun t i=> watch (D.scope i) (recruit (box (a t)) P)) := by
    funext t; rw [Function.comp_apply, show f t= _ from (rfl : f t=(D.purse P,a t)), way, ← D.equal]; rfl
  rw [he]; unfold align slope; change HasDerivAt _ (u (A.D (tang (box v) X.val P))) _; rw [← D.equal]; exact D.stamps.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_pi.mpr (show ∀ i:Fin D.n,HasDerivAt _ (watch (D.scope i) (tang (box v) X.val P)) (0:ℝ) from fun i=> closed_move P _ _ _))
lemma unpin (H:A.Prepared): D.delta D.opening=1:=by
  ext1 t; obtain ⟨p,rfl⟩:= (guide G d).surjective t; rw [opening,order,align,map_zero,regular A H]; rfl
end Fray
end YM.XSpace.Normalize
