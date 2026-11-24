import YM.OPE.Compatible.Cum.Tuber
/-!
# Γ branch per extra. Decouple before merging
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J:Type}{N:Side}[Fintype I]
variable {s:Finset J}[DecidableEq J]{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{X:J→Option (Site N)} {a b:Site N}{c y g κ σ l:ℝ}{Ω:Row I I}{C:ℕ→ℝ}{p e k d t n m h:ℕ}{F H:Curtain I}{r:J→ℝ}{x:deck I N}
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "K!"=>Flume.Script.Tab I N
variable (μ:Measure E)(L:Law E)(R:Script I (e+d+1))(a:Site N)(Z:E→L[ℝ] deck I N)(x:deck I N)
def Kilt (R:Script I (e+d+1))(a:Site N)(L:Law E)(Z:E→L[ℝ] deck I N)(x:deck I N)(P:Tensor.T (deck I N) ℝ (n+p))(j:Fin p): E→ℝ:=∑ i:Flume.Script.Tab I N,(FTl e d (orchestra R a) x x (deltaH i) Z) * φx x x Z P (L.inverse (Ferry Z i)) j
abbrev Uric (i:J)(f:J→E→ℝ)(P:Tensor.T (deck I N) ℝ (n+p)):= ∑ j:Fin p,Tap μ L f (Kilt R a L Z x P j) (s.erase i)
end
-- general lemma. choose h : v i=P before.
def Quest (v w:J→ℕ)(s:Finset J)(κ σ:ℝ)(m n d e:ℕ)(C:ℕ→ℝ)(I: Type)[Fintype I](i:J)(p:ℕ):Prop:= ∃ D:ℝ,0 ≤ D ∧ ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I),Ω.strip σ κ →∀ (N:Side)(Q:∀ i,Script I (w i+v i))(Z:E→L[ℝ] deck I N)(a:Site N)(X:J→Option (Site N))(c:ℝ)(x:deck I N),Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c→∀ r:J→ℝ,coversB v w Q m r s→forall (P:Script I (w i+p)),soot m P (r i)→ Globe (w i+p) (X i) x P Ω L C Z a c m→∀ R: Script I (e+d+1),∀ b:ℝ,soot m R b →∀ k, Rollup v w s (d+1) e ≤ k→ let F:= (if (LightX (X i)) then Once Ω (Shell.Hall Ω v w Q (LightX ∘ X) (s.erase i)) e d R (w i) p P else 0:Curtain I); Bins F∧ Mold (Uric (s:=s) μ L R a Z x i (Fig v w Q X c x Z) (Vx (X i) P c) (p:=p) (n:=w i)) (Flair F k x a) (D*b*Visit r s*Gates x s v w e (d+1)) N n
lemma tryst (j:J)(hg:j∈s)(hp:p=v j)(hc:0≤ C)(hK:0≤κ)(hσ:0<σ)(hv:∀ t u,Texter v w (s.erase j) κ σ m n t u C I)(hk:n+HueS s≤m): Quest v w s κ σ m n d e C I j p:=by
      cases p
      next=>
         refine ⟨0,le_rfl,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z a X c x h r he P hS hH R b hB k hy F; rw [zero_mul,zero_mul,zero_mul, show F=0 from ?_,flair0]; swap; · unfold F; split<;> rfl
         refine ⟨binZ,?_⟩; unfold Uric; simp only [Finset.univ_eq_empty,Finset.sum_empty]; exact moldZero _ le_rfl
      next p=>
        obtain ⟨b,hb,H⟩:= hv (d+p) (e+w j); let a:= (e+d+(w j+p)); let c:=Aroma J I (w+v) (C 0) a (s.erase j); have hc' :0≤ c:=aroma0 (hc 0); let z:=widthCost σ m * κ * ((3*(w j+p)+2:ℕ):ℝ)^m; have hz : 0 ≤ z:=by unfold z; have h:= zero_le_one.trans (widthCost_ge hσ m); positivity
        let u:ℝ:=3^m*(C m); have hu:0 ≤ u:=mul_nonneg (by positivity) (hc _); let D:= max (c*u) (b*z); have hD:0≤ D:=(mul_nonneg hb hz).trans (le_max_right ..)
        refine ⟨(p+1:ℕ)*D,by positivity,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z i X B x h r he P hP hG R m' hR k hL F; let f:=Fig v w Q X B x Z; let C':=Vx (X j) P B; let t:= s.erase j; let X':=LightX ∘ X; let A:=Shell.Hall Ω v w Q X' t; let W(m:Fin (p+1)):= Kilt R i L Z x C' m
        let g:= Gates x s v w e (d+1); let q:=(1+‖x‖)^(Rollup v w t (d+p) (e+w j)); have hp1: Rollup v w t (d+p) (e+w j) ≤ Rollup v w s (d+1) e:=by have h:=rollingB (e:=e) (d:=d) (v:=w) hg p hp.symm; unfold t;omega
        have hq:q ≤ g:=pow_le_pow_right₀ (by simp) hp1; let Y:= Visit r s; let V':= Visit r t; have hy:0 ≤ Y:= Visit0 he; have hb':=Sack.coins hR; have hV: Y=r j*V':= (Finset.mul_prod_erase _ _ hg).symm; have hs':t ⊆ s:= erase_subset ..
        cases hX:X j with
        | none=>
          let P'(u:Fin (p+1)):=mitt e d (w j) p R P u Ω; have hW:Rookie L Z Ω x P B:=by simpa only [Globe,hX] using! hG
          have hh(i':Fin (p+1)): soot m (P' i') (m'*(r j)*z):=(styleM R P hR hP hΩ hσ hK i').tips (le_of_eq (by unfold z; ring)); have he' : coversB v w Q m r t:=fun l ht=> he l (hs' ht); have ht(i:Fin (p+1)): Bins (A (d+p) (e+w j) (P' i)):= Hall_bins σ κ hΩ hσ hK he' _ (hh i)
          have hC : F=∑ i:Fin (p+1), A (d+p) (e+w j) (P' i):=by unfold F; rw [hX,if_pos (by simp [LightX]),once_plus]
          have h₁(i':Fin (p+1)): Mold (Tap μ L f (W i') t) (Flair (A _ _ (P' i')) k x i) (D*m'*Y*g) N n:=by
               have hs: W i'=SX x x Z (orchestra (P' i') i) (d:=d+p) (e:= e+w j):=by
                     funext l; unfold W C'; rw [hX]; unfold Kilt; rw [Finset.sum_apply]; exact (under L Z Ω x i B P R l i' (sootS hR) (sootS hP) (show Whole Ω from ⟨σ,κ,hσ,hΩ⟩) hW).trans (scriptV i (P' i') _ (sootS (hh i'))).symm
               rw [hs]; apply le_trans (show Mold _ _ (b*(m'* (r j)*z)* V'*q) N n from H E μ L Ω hΩ N Q Z i X B x (Buds.nat x h hs') r he' _ _ (hh i') _ (hp1.trans hL)); rw [show b*(m' * r j * z)* V'= b*z*m'*Y from by rw [hV];ring]; refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hb') hy) hq (pow_nonneg (by positivity) _) (by positivity)
          rw [hC]; refine ⟨Bins.falls _ fun i _=> ht i,?_⟩;rw [flairS k x i _ (fun i _=>ht i)]; rw [← hX]; apply (moldSum (s:=univ) (fun i _=>h₁ i)).trans_eq; rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; unfold Y g;ring
        | some t'=>
          have hc1 : Cold i t' (Oriel L Z) (C m) m:=by rw [hX] at hG; exact hG m le_rfl
          have h₁(j':Fin (p+1)): Mold (Tap μ L f (W j') t) 0 (D*m'*Y*g) N n:=by
                 have ht: BeamS (grain N m • (W j')) (u*m'*r j) (clockY x Z) a:=by unfold W C'; rw [hX]; exact extPay R P i t' x j' hc1 (hc m) hR hP
                 unfold Mold; rw [sub_zero]; apply (payJ (Buds.nat x h hs') (fun l hl=> he l (hs' hl)) ht (by have h:= Sack.coins hP; positivity) (show n+HueS t≤m from (Nat.add_le_add_left (by unfold HueS; have he:= card_le_card hs'; omega) _).trans hk)).trans; rw [show a+Mani (w+v) t=Rollup v w t (d+p) (e+w j) from ?_]; swap; · rw [carveEq];unfold a Rollup; omega
                 change c*q* (u*m' *r j)* V'≤ _; rw [show c*q*(u*m'*r j)*V'=c*u*m'*Y*q from by rw [hV];ring]; exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) hb') hy) hq (pow_nonneg (by positivity) _) (by positivity)
          rw [show F=0 from ?_,flair0]; swap; · unfold F;rw [hX, if_neg (by simp [LightX])]
          refine ⟨binZ,?_⟩; have he:= moldSum (s:=univ) (fun i _=>h₁ i); simp only [sum_const_zero, sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at he; rw [← hX]; apply he.trans_eq; unfold Y g;ring
end YM.OPE.Libra.Shell
