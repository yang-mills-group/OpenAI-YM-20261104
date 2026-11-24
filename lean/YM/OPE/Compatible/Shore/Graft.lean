import YM.OPE.Compatible.Shore.Wedge
/-!
# Signed extraction. Superpose into an existing slot. Contracting
many options uses per-mode route toll, representing true names.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Mirror Deb
open scoped Topology BigOperators Classical
variable {V I J W X : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype W][DecidableEq W]
    {G:Gauge}{n : Side}{H:RG.History G}{Q:Rep G n}
variable (x:I)(q:W→ℂ)(P:Ensemble V)
def foldTo (x:I): I⊕W→I := Sum.elim id fun _=>x
local notation "F"=>foldTo (W:=W) x
-- orientation scalar at destination
def dyes (q:W→ℂ): I⊕W→ℂ := Sum.elim 1 q
local notation "A"=> atopBy V (foldTo (W:=W) x)
local notation "V!"=> spices P (dyes (I:=I) q)
local notation "T"=> Names V (I⊕W)
local notation "P!"=> Deb.portion (atopBy V (foldTo (W:=W) x)) (spices P (dyes (I:=I) q))
local notation "U"=>sendAll (atopBy V (foldTo (W:=W) x)) (spices P (dyes (I:=I) q))
omit [Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype W][DecidableEq W] in
lemma dye_zero (i:V)(v:I): (spices P (dyes (I:=I) q) (i,.inl v))=1:=by unfold spices Ensemble.echo; unfold scalar; change (ite _ (star 1) 1)=1; split<;> simp
omit [DecidableEq W] in
lemma branching {X:Type} [AddCommGroup X] [Module ℂ X] (y:V×(I⊕W)→X)(i:V)(j:I):
    Deb.portion (atopBy V (foldTo (W:=W) x)) (spices P (dyes (I:=I) q)) y (i,j)=y (i,.inl j)+ if j=x then ∑ k:W,(P.echo (q k) i) • y (i,.inr k) else 0:=by
   unfold Deb.portion; rw [Fintype.sum_prod_type,sum_eq_single i _ (by simp)]; swap
   · intro b _ he; apply sum_eq_zero; intro z _; exact if_neg (fun h=> he (congr_arg Prod.fst h))
   rw [Fintype.sum_sum_type]; congr 1
   · rw [sum_eq_single j]; rw [if_pos (show A (i,Sum.inl j)=(i,j) from rfl),dye_zero,one_smul]; intro b _ hb; exact if_neg (fun he=>hb (congr_arg Prod.snd he)); simp
   by_cases he:j=x; · subst j; rw [if_pos rfl]; apply sum_congr rfl; intro z _; exact if_pos rfl
   rw [if_neg he]; exact sum_eq_zero fun k _=>if_neg (fun h=>he (congr_arg Prod.snd h.symm))
variable {E:V→Site n}{v:I⊕W→ Stem V G n}
    {a:I⊕W→ℝ}{b:I→ℝ}{e:ℝ}
lemma super {Y: Config G n→ Marker.Poly (Names V (I⊕W))}{χ:Guard (Names V (I⊕W))}{χ':Guard (Names V I)}
    (H:Owned χ Q E P v a e Y)(h:∀ i,χ'.safe (landed A i) → Flat A i → χ.safe i)(z:I→ Stem V G n)
    (hx:∀ i,Marked Q E P (z i))(hB:∀ i,0<b i)
    (hM:∀ i,(z (F i)).home=(v i).home) (hS:∀ i,b (F i)* ‖dyes q i‖≤ a i)
    (hL: lights z=P! (lights v))(hK: Stem.ink z Q=P! (Stem.ink v Q)): Owned χ' Q E P z b e (sendAll (atopBy V (foldTo (W:=W) x)) (spices P (dyes (I:=I) q)) ∘ Y):=by
    obtain ⟨Y',hY,hZ,h'⟩:= H.issues
    let u:= U ∘ Y'; have hv: Integrable u (prior G _):= ((U).toContinuousLinearMap.restrictScalars ℝ|>.integrable_comp hY)
    refine ⟨u,hv,fun i _ hh=> deliver_safe _ _ (hZ i) (fun a he hi=>h a hi he) _ hh,hx,hB,?_⟩
    rw [hL,hK]; exact deliver_marked F _ P h'.ship (funext fun i=> congr_fun (hM i.2) i.1) (fun i=>hB i.2) (fun i=> by rcases i with ⟨i,a'⟩; unfold spices; rw [P.price (dyes q a') i]; exact hS _)
end YM.MergeProof.Ribbons.ManyCopies
