import YM.Qlocal.Canopy.Settle
/-!
 # Accuracy in Switch.Log, full occupation & at retargeted amplitudes
 geometry & analytic tallies later. R consumes TP.Picture & positivity.Act.Cluster source not this Ring.-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy
open Function Finset Filter Topology Merge Switch
open AllOrder Ker Laplace Laplace.SigmaP Response Catch Catch.Clock PositionX.Jet
open ConnectedActivityE6 Blaze Brush PertExtension PertExtension.Series
open PhysicalNext Repeat Fare Lapis
open scoped Topology ContDiff BigOperators Classical
variable {ι : Type*} {S: Catch.Clock ι}{X:ι→ Type} [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)]
    {j k q n m r:ℕ} {d t:ι→ℝ}{x:∀ i,X i}
namespace Lithe
variable {σ:Type}[Fintype σ]
-- Clock picks AFTER marker Census, power ledger.Inl.One.Fixed rank.AUX.
abbrev Emmons (X:ι→Type)(σ:Type):=(i:ι) → X i → Button.Book σ
abbrev Bloom (X:ι→Type)(σ:Type):=(i:ι) → X i → Score σ
variable (a b: Bloom X σ)(P Q:Emmons X σ)
abbrev Vintage (S:Catch.Clock ι)(t d:ι→ℝ)(j k:ℕ) (P:Emmons X σ)(a:Bloom X σ)(x:∀i,X i): Prop:=∀ P0:Finset σ, Sail S t d j k (fun i x=> swap (P i x) P0) (fun i x=> a i x P0) x
local notation "H"=> Vintage S t d j k
set_option quotPrecheck false
local notation "π"=>Sail S t d j k
variable {P Q a b}
variable (ht : S.Meter t (-(1/2))) (hd:∀ᶠ i in S.rail,0≤ d i)
namespace Vintage
include hd
lemma flash : H (fun i (_:X i)=> Button.neutral σ) (fun _ _=> bench ∅ 1) x :=by
 intro W; refine (Sail.cross (Sail.free (x:=x) hd (bench ∅ 1 W)) (?_) (?_)); swap;· rfl
 ext i x t; change (just (bench ∅ 1 W)) t= _; unfold swap Button.neutral just; by_cases hx:t=0 <;> simp [hx]
variable (hp:Vintage S t d j k P a x)(hq:Vintage S t d j k Q b x)
include hp
omit hd
lemma scales (v:ι→ℝ)(hv:S.Meter v 0): H (fun i x=> v i • P i x) (fun i x=> v i • a i x) x:= fun t=> (hp t).scaled v hv
include hq
lemma subing : H (P-Q) (a-b) x:= fun p=> (hp p).emerged (hq p)
lemma assemble : H (P+Q) (a+b) x:= fun p=> (hp p).earned (hq p)
include hd ht
lemma register : H (fun i x=> Button.pledge (P i x) (Q i x)) (fun i x=> comb 0 (a i x) (b i x)) x:= by
 intro p
 let f (j:Finset σ): Tape X:= fun i x=> swap (P i x) j; let h (j:Finset σ): Tape X:=fun i x=>swap (Q i x) (p\j); let k (j:Finset σ) i (x:X i):=a i x j * b i x (p\j)
 have hqℓ(j:Finset σ):Sail S t d _ _ (fuse (f j) (h j)) (k j) x:= Sail.united ht hd (hp j) (hq (p\j));
 apply Sail.cross (Sail.quota hd p.powerset _ _ (fun i _=> hqℓ i)); swap; · ext1 i; ext1 y; simp_rw [Finset.sum_apply,Button.combPath]; rfl
 ext i u y; simp only [Finset.sum_apply]; simp_rw [fuse, plus_sum,swap,Button.pledge,Finset.sum_apply,Button.combPath]; apply Finset.sum_comm
omit hq
open Button RGComparison01.Slate
lemma enroll (m:ℕ): H (fun i x=> Button.knot (P i x) m) (fun i x=>stack (a i x) m) x:= by induction m with
 | zero=> simp_rw [Button.knot, stack]; exact flash hd
 | succ m ih=> simp_rw [Button.knot,stack]; exact register ht hd ih hp
omit hp ht
lemma sick : H (0:Emmons X σ) 0 x:= fun P=> Sail.dark hd
lemma booked {δ:Type*}(s:Finset δ)(P:δ→Emmons X σ) (a:δ→Bloom X σ)(h:∀ i∈s,H (P i) (a i) x) : H (∑ i∈s,P i) (∑ i∈s,a i) x:= by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact sick hd
 | insert i u hi ih=> rw [sum_insert hi,sum_insert hi]; exact assemble (h _ (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
include hp ht
-- no assumption `k=0`; still pointwise truncation at k. actual tally property from true sectors.
lemma market (m:ℕ): H (fun i x=> Button.connect m (P i x)) (fun i x=>Earmark (a i x) m) x:= by
 let A(i:ι)(x:X i):=Button.neutral σ - P i x; let b(i:ι)(x:X i):=bench ∅ 1-a i x; let Q(j:ℕ)(i)(x:X i):= tax j • (Button.knot (A i x) (j+1)); let z(j:ℕ)(i)(x:X i):=tax j • stack (b i x) (j+1); have hz(j:ℕ): Vintage S t d _ _ (Q j) (z j) x := (scales (enroll (P:=A) (a:=b) ht hd (subing (flash hd) hp) (j+1)) (fun _=>tax j) (Meter.const S _))
 apply Eq.mp ?_ (booked hd (range (m+1)) Q z (fun i _=> hz i)); unfold Button.connect Earmark; apply congr_arg₂ (fun kL g=>Vintage S t d _ _ kL g x) _ _;
 all_goals ext1 i; funext y; simp_rw [Finset.sum_apply]; try rfl
omit hd ht
variable (P' : ι→ σ→ℝ) (hP : ∀ i:σ,S.Meter (fun j=> P' j i) 0)
include hP
-- Products of finitely many zero-order metered weights are again metered at order zero.
omit hp in
lemma weightS (A:Finset σ): S.Meter (fun i=>∏ j∈ A, P' i j) 0:=by
 induction A using Finset.induction with
 | empty => simp only [Finset.prod_empty]; exact Meter.const S 1
 | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact ((hP i).mul ih).weak (by simp)
lemma healed : H (fun i x=> Button.polishP (P' i) (P i x)) (fun i x=> Button.polish (P' i) (a i x)) x:=fun s=> (hp s).scaled (fun i=>∏ j∈ s,P' i j) (weightS P' hP s)
end Vintage
end Lithe
end YM.Qlocal.Canopy
