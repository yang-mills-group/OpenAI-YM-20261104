import YM.QuadraticLocal.Sunrise.Focus
/-!
# Pure multiplicities. Project inside width budget
 use **selector over real full polynomial** rather than normed complex;
 still retaining complex probes via independent δ variables later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Focus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push
open scoped BigOperators Topology Classical ContDiff
variable {G: Gauge} {n m:Side} {V:Type} {ι α β:Type}[Fintype α][Fintype β][Fintype ι][DecidableEq ι] (T:Finset ι) (k:ℕ)
variable {a C D:ℝ}
local notation "Λ"=> Focus.Assignment ι k
local notation "J"=> ((α⊕ι))
local notation "U"=> rule (α⊕ι) n
local notation "σ"=> sustain (α:=α) (n:=n)
local notation "mom" i:max=> dayV k ∘ (i:Λ)
-- multiplicity recursive. V coordinate spectator. do not require DecEq V.
def calls (s:J) : ι→ℕ:= Sum.elim (fun _ _=>0) (fun x i => if x=i then 1 else 0) s
def tally (l:Slip (V×(α⊕ι))) : ι→ℕ := (l.map (calls ∘ Prod.snd)).sum
local notation "Y'" L:max i:max=> tally L i
lemma stamped (v:V×J)(L:Slip (V×J)) (i:ι) : tally (v::L) i= calls v.2 i + tally L i:=rfl
lemma heightL (L:Slip (V×J))(i:ι): tally L i ≤ L.length:=by
 induction L with
 | nil=> exact Nat.le_refl 0
 | cons v L ih=>
    rw [stamped,List.length_cons]; have h:calls v.2 i ≤ 1:= by obtain ⟨y,x|x⟩:= v; exact Nat.zero_le _; unfold calls; dsimp; split <;> omega
    omega
-- Keep precise mode, counts.E.Doc.
def Depicted (L:Slip (V×(α⊕ι))) := ∀ i:ι, tally L i= if i∈T then 1 else 0
lemma dictated (w:Site n)(L:Slip (Point (J))) : tally (L.map (stood w))=tally L:=by induction L with | nil=>rfl | cons v L ih=> rw [List.map_cons]; funext i; rw [stamped,ih]; rfl
lemma pictured (w:Site n)(L:Slip (Point (J))) : Depicted T (L.map (stood w)) ↔ Depicted T L:=by unfold Depicted; rw [dictated w L]
local notation "Lℓ"=> Slip (Leaf n (J))
lemma callPose {R:Type*}[CommMonoid R](p:ι→R)(i:J) : (∏ x:ι,p x^calls i x)= i.elim (fun _=>1) p:= by cases i <;> simp only [calls,Sum.elim_inl,Sum.elim_inr,pow_zero,Finset.prod_const_one]; simp [ite_pow]
lemma spent (f:ι→ℝ)(v:U)(L:Lℓ): paid ((σ f) v) L= (∏ j:ι,f j^tally L j)*paid v L:= by
 induction L with
 | nil=> simp [paid,tally]
 | cons x L ih=>
    change _*paid _ L=_*(_*paid v L); simp_rw [stamped,pow_add]; rw [Finset.prod_mul_distrib, look_at,ih,callPose f x.2]; unfold which; ring
-- indicator exact; independent price simplex.Real
lemma certified (L:Lℓ)(he:L.length≤k)(v:U) : lens T k (fun w:U=> paid w L) v= if Depicted T L then paid v L else 0:= by
 let Y(i:ι)(x: Root k):= song T i k x * dayV k x ^ tally L i; let g (θ:Λ):= ∏ i:ι,Y i (θ i); have he' θ: cap T k θ *paid ((σ (mom θ)) v) L = g θ * paid v L := by rw [spent,cap,← mul_assoc,← Finset.prod_mul_distrib]; rfl
 rw [billK,Finset.sum_congr (s₂:=Finset.univ) rfl (fun x _=> he' x),← Finset.sum_mul, show ∑ t,g t= ∏ i,∑ j,Y i j from (Fintype.prod_sum ..).symm]; let F(i:ι):= sign T i k
 have hx (i:ι): ∑ j,Y i j= _:= timing T k i _ ((heightL L i).trans he) -- arg order?
 have hh (i:ι): (sign T i k).val=(if i∈T then 1 else 0):= by unfold Focus.sign; split <;> rfl
 simp_rw [hx, hh]; split; next ht=> simp [show ∀ j, tally L j=if j∈T then 1 else 0 from ht]
 next he=> unfold Depicted at he; push_neg at he; obtain ⟨i,hi⟩:= he; rw [Finset.prod_eq_zero (i:=i) (mem_univ _) (if_neg hi),zero_mul]
lemma invoiceCertified (L:Slip (Point (J))) (h:L.length≤ k) (x:Site n) (u:U): lens T k (invoice x L) u=if Depicted T L then invoice x L u else 0:= by unfold invoice; rw [certified T k _ (by rwa [List.length_map]), pictured]
end YM.QuadraticLocal.Sunrise.Focus
