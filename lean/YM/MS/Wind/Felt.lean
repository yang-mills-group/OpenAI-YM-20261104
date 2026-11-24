import YM.MS.Wind.Desk
/-!
# Picard flow at one-line, fixed order and all t

Neumann series truncates at rank cut. Hess and cubic use at higher orders. Use for quantitative patch at rank r. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H:Flow G}{P Q:Pack G}{b:Bool}{u v r:ℤ}{I:Type}
abbrev Wiref (G:Gauge):= lapidus (Cpu G)
abbrev treeP (G: Gauge):= busy (Cpu G)
abbrev volt (G:Gauge): Flow G →ₗ[ℂ] Flow G := (tonic G).comp (Wiref G)
private lemma lift_level (hk: TouchF F) (hr: Rank F r)(i:ℕ): Rank ((volt G^i) F) (r- (i:ℤ)*2)∧ TouchF ((volt G^i) F):= by
    induction i with
    | zero=> simpa only [pow_zero,Module.End.one_apply,Nat.cast_zero,zero_mul,sub_zero] using And.intro hr hk
    | succ n ih=>
        let T:= (volt G^n) F; have he := lapid_touch ih.2 (main_f G);
        rw [pow_succ', Module.End.mul_apply, show volt G T=coast (Wiref G T) from congr_arg (fun k=>k) (tonic_at he)]; refine ⟨?_,deskLift he⟩; rw [show r- (↑(n+1:ℕ):ℤ)*2=(r- (n:ℤ)*2)-2 by omega]; exact desk_max (lapid_max ih.2 (main_f G) ih.1)
lemma interest (hP:Fees b u P)(i:ℕ): Fees b u (fun x=> (volt G^i) (P x)):= by
   induction i with| zero=> simpa using hP| succ k ih=> rw [pow_succ']; exact tonicPack (lapidPack ih)
-- forced station derivative eq

def Sat (A : Law G)(F H:Flow G): Prop:= F 0=A ∧ ∀ t:ℝ, Zip F (Wiref G F t+H t) t
lemma Sats {A:ℝ→ Law G} {H:Pack G}(hA: Fees b u (fun x _=> A x))(hH: Fees b u H): ∃ F':Pack G, Fees b u F' ∧ ∀ x, Sat (A x) (F' x) (H x):= by
   let Q (x:ℝ): Flow G:= (fun _=>A x) + tonic G (H x); have hZ : Fees b u Q:= hA.sum2 (tonicPack hH)
   obtain ⟨v,hq⟩:= hZ.pay; let M := Finset.range (v+1); let P (i:ℕ)(x:ℝ):=(volt G^i) (Q x); let R:= ∑ i∈M,P i; have he : Fees b u R:= Fees.sum _ (fun i _=> interest hZ i); refine ⟨R,he,fun x=>?_⟩
   have hs : R x= Q x+(volt G) (R x):= by
       unfold R; rw [Finset.sum_apply, map_sum]; simp_rw [show ∀ i,volt G (P i x)=P (i+1) x from fun i=> by unfold P; rw [pow_succ']; rfl]; unfold M
       conv_lhs=>rw [Finset.sum_range_succ']
       conv_rhs=> rhs; rw [Finset.sum_range_succ]
       rw [show P (v+1) x=0 from Rank.gone (lift_level (hZ.stay x|>.joint) (hq x) (v+1)).1 (by omega),add_zero,add_comm]; simp [P] -- inspect conv
   -- P relation to additive result
   let T:= Wiref G (R x)+ H x; have ht : TouchF T:= (lapid_touch (he.stay x|>.joint) (main_f G)).add (hH.stay x|>.joint); have hh : R x=(fun _:ℝ=>A x)+coast T:= by
        rw [← tonic_at ht]; unfold T; rw [map_add]; nth_rw 1 [hs]; unfold Q; rw [LinearMap.comp_apply, add_comm (tonic G (Wiref G (R x)))]; exact add_assoc .. ;  -- may rewrite both R
   rw [Sat]; refine ⟨?_,fun t i=>?_⟩; · rw [hh,Pi.add_apply,show coast T 0=0 from funext fun i=>by simp [coast],add_zero]
   have hJ (t:ℝ) : R x t i=A x i+∫ s in 0..t,T s i:= congr_fun (congr_fun hh t) i; change HasDerivAt (fun t:ℝ=>R x t i) (T t i) t; simp_rw [hJ]; exact (hfun ((ht.at_const (fun s:ℝ=>s) i contDiff_id).continuous) t).const_add _ -- maybe order
end YM.MS.Wind
