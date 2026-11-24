import YM.WilsonCoeffUV.Marked.Step.MarkerAlgebra
/-!
# Source logs use connected heat with drift (normalized denominator)
Exact PDE computation commutes with the Euler source log. Two-sided G (don't
normalize factor by transpose unless symmetry assumed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer
open scoped BigOperators
variable {ι:Type}[DecidableEq ι]{U:Type}{J K S T:Finset ι}
variable [Fintype U]
scoped instance : IsAddTorsionFree (Ink U):= ⟨by
   intro n hn x y hp; ext1 t; apply (smul_right_inj (M:=POL U) hn).mp; exact (map_nsmul (coeff t) n x).symm.trans ((congr_arg (coeff t) hp).trans (map_nsmul (coeff t) n y))⟩
abbrev Polar (ι U:Type):= Sac ι (Ink (Option U))
omit [Fintype U] in
lemma tides_pair (M L:Polar ι U)(h:Equation M L)(u v:Option U):
     (brush u) ∘ ((brush v) ∘ M)=shells (fun S=> brush u (brush v (L S))) M + shells (shells (brush v ∘ L) (brush u ∘ L)) M:=by
    rw [h.track _];
    rw [scan_map,h.track,littoral]; rfl

lemma tendon (G:Matrix U U ℝ)(L M:Polar ι U)(S:Finset ι):
   ∑ a:U,∑ b:U,(G a b/2) • shells (brush (some a) ∘ L) (brush (some b) ∘ M) S= ∑ i∈S.powerset, goLip G (L i) (M (S\i)):=by
    unfold shells; simp_rw [goLip,Finset.smul_sum]; rw [Finset.sum_comm (s:=S.powerset)]
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; rfl
lemma comLap (G:Matrix U U ℝ)(M L:Polar ι U)(h:Equation M L): goLap G ∘ M=shells (goLap G ∘ L + fun S=>∑ J∈S.powerset, goLip G (L J) (L (S\J))) M:=by
    funext S; rw [shells_l,Pi.add_apply,comp_apply]
    let f (u:U):=brush (some u); let E (a b:U)(J:Finset ι):= f a (f b (L J)); let X (a b:U):= shells (⇑(f a) ∘ L) (⇑(f b) ∘ L); let W (J:Finset ι):= ∑ i∈J.powerset,goLip G (L i) (L (J\i))
    have hh (a b): E a b=(f a) ∘ ((f b) ∘ L):= rfl
    have he (a b:U): brush (some a) (brush (some b) (M S))= shells (E a b) M S+shells (X a b) M S:=by rw [hh]; unfold X; rw [←shores (f b ∘ L)]; exact congr_fun (tides_pair M L h _ _) _
    have ht : ∀ J:Finset ι,W J=∑ a:U,∑ b:U,(G a b/2) • X a b J:= fun J=>(tendon G L L J).symm
    simp_rw [spelt, he,smul_add, Finset.sum_add_distrib]; congr 1
    · rw [shells]; simp_rw [comp_apply,spelt]; simp_rw [Finset.sum_mul,shells, Finset.smul_sum, smul_mul_assoc]; rw [Finset.sum_comm (s:=S.powerset)]; exact Finset.sum_congr rfl fun a _=>by rw [Finset.sum_comm]
    change _ = shells W M S; rw [shells]; simp_rw [ht,Finset.sum_mul,shells, Finset.smul_sum,smul_mul_assoc]; rw [Finset.sum_comm (s:=S.powerset)]; exact Finset.sum_congr rfl fun a _=>by rw [Finset.sum_comm]
lemma comLip (G:Matrix U U ℝ)(D:Ink (Option U))(M L: Polar ι U)(h:Equation M L): goLip G D ∘ M= shells (goLip G D ∘ L) M:=by
    have he (J:Finset ι)(b:U): brush (some b) (M J)=shells (brush (some b) ∘ L) M J:=congr_fun (Equation.track M L h (brush (some b))) _
    funext S; rw [shells]; simp_rw [comp_apply,goLip, he,shells,Finset.sum_mul,Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,mul_assoc, comp_apply]; rw [Finset.sum_comm (s:=S.powerset)]; exact Finset.sum_congr rfl fun a _=>by rw [Finset.sum_comm]

theorem logPDE (G:Matrix U U ℝ)(D:Ink (Option U))(L M: Polar ι U)(h:Equation M L)(hp:∀ S,brush none (M S)=goLap G (M S)+goLip G D (M S)+goLip G.transpose D (M S)):
       ∀ S,brush none (L S) = goLap G (L S)+goLip G D (L S)+goLip G.transpose D (L S) + ∑ J∈S.powerset, goLip G (L J) (L (S\J)) :=by
   have H : brush none ∘ L=((goLap G ∘ L + goLip G D ∘ L)+ goLip G.transpose D ∘ L)+(fun S=> ∑ J∈S.powerset, goLip G (L J) (L (S\J))):=by
       have he : brush none ∘ M=(goLap G ∘ M + goLip G D ∘ M) + goLip G.transpose D ∘ M:=funext hp
       rw [h.track,comLap G M L h,comLip G D M L h,comLip G.transpose D M L h] at he
       apply shells_cancel M _ _ h.1; simp_rw [he,shells_l]; abel
   intro S; exact congr_fun H _
end YM.WilsonCoeffUV.Wheel.Mark
