import YM.OPE.Compatible.Cum.Streak
/-! # Uniform self portions paid. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J: Type}{N:Side}[Fintype I]
variable {s:Finset J}[DecidableEq J]{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{X:J→Option (Site N)} {a b:Site N}{c y g κ σ l:ℝ}{Ω:Row I I}{C:ℕ→ℝ}{p e k d t n m h:ℕ}{F H:Curtain I}{r:J→ℝ}{x:deck I N}
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "K!"=>Flume.Script.Tab I N
variable (μ:Measure E)(L:Law E)(R:Script I (e+d+1))(a:Site N)(Z:E→L[ℝ] deck I N) (x:deck I N)
def Twang (R:Script I (e+d+1))(a:Site N)(L:Law E)(Z:E→L[ℝ] deck I N)(x:deck I N)(j:Fin d):E→ℝ:= ∑ i:K!,φx x x Z ((orchestra R a).curryLeft (deltaH i)) (L.inverse (Ferry Z i)) j
abbrev Urge (f:J→E→ℝ):= ∑ j:Fin d,Tap μ L f (Twang R a L Z x j) s
end
omit [DecidableEq J] in lemma carveEq : Mani (w+v) s=∑ i∈s,(v i+w i):=by unfold Mani; exact Finset.sum_congr rfl fun i _=>Nat.add_comm ..
omit [DecidableEq J] [Fintype I] in lemma Visit0 (hc:coversB v w Q m r s): 0 ≤ Visit r s:= prod_nonneg fun i hi=> Sack.coins (hc i hi)
abbrev Gates (x:deck I N)(s:Finset J)(v w:J→ℕ)(e d:ℕ):=(1+‖x‖)^(Rollup v w s d e)
def swims (v w:J→ℕ)(s:Finset J)(κ σ:ℝ)(m n d e:ℕ)(C:ℕ→ℝ)(I: Type)[Fintype I]:Prop:= ∃ D:ℝ,0 ≤ D ∧ ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I),Ω.strip σ κ →∀ (N:Side)(Q:∀ i,Script I (w i+v i))(Z:E→L[ℝ] deck I N)(a:Site N)(X:J→Option (Site N))(c:ℝ)(x:deck I N),Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c→∀ r:J→ℝ,coversB v w Q m r s→∀ R: Script I (e+d+1),∀ b:ℝ,soot m R b →∀ k, Rollup v w s (d+1) e ≤ k→ let F:= WalkK Ω e d R (Shell.Hall Ω v w Q (LightX ∘ X) s); Bins F∧ Mold (Urge (s:=s) μ L R a Z x (Fig v w Q X c x Z)) (Flair F k x a) (D*b*Visit r s*Gates x s v w e (d+1)) N n
lemma swimming (hc:0≤ C) (hK:0≤κ)(hσ:0<σ)(hv:∀ i<d, Texter v w s κ σ m n i e C I)(hp:n+HueS s≤m): swims v w s κ σ m n d e C I:=by
      cases d
      next =>
         refine ⟨0,le_rfl,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z a X c x h r hb R b hB k hq F; refine ⟨(show F=0 from soak_nil ..).symm ▸ binZ,?_⟩; rw [zero_mul,zero_mul,zero_mul, show Urge (s:=s) μ L R a Z x (Fig v w Q X c x Z) (d:=0)=0 from ?_,show Flair F k x a=0 from ?_]; exact moldZero 0 le_rfl
         swap
         · exact sum_eq_zero fun i _=> Fin.elim0 i
         rw [show F=0 from soak_nil ..];exact flair0 ..
      next d=>
        obtain ⟨D,hD,H⟩:= hv d (by omega); let c:=Aroma J I (w+v) (C 0) (e+d) s; have hc₁: 0 ≤ c:= aroma0 (hc 0); let c':=8^m*widthCost σ m*κ+3^m*C m; have hc':0≤c':=by unfold c'; have hK':0 ≤ C m:= hc m;have h:=zero_le_one.trans (widthCost_ge hσ m); positivity
        refine ⟨(d+1:ℕ)*(c*c'+D*κ),by positivity,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z a X b x h r hb R w' hB k hx F
        let f:= Fig v w Q X b x Z; let V:=Shell.Hall Ω v w Q (LightX∘ X) s; let P(i:Fin (d+1)):=knots e d R i Ω; have he : F=∑ i:Fin (d+1),V d e (P i):= soak_plus ..; have hp1(i:Fin (d+1)): soot m (P i) (w'*κ):=styleR R hΩ hσ.le hK hB i; have hk(i:Fin (d+1)):Bins (V d e (P i)):= Hall_bins σ κ hΩ hσ hK hb _ (hp1 i); let g:= Gates x s v w e (d+1+1); let Y:= Visit r s; have hy:0 ≤ Y:= Visit0 hb; have ha:= Sack.coins hB; let q:=(1+‖x‖)^(Rollup v w s d e); have hQ: Rollup v w s d e ≤ Rollup v w s (d+1+1) e:=by unfold Rollup;omega
        have hq:q ≤ g:= pow_le_pow_right₀ (by simp) hQ
        have he'(i: Fin (d+1)): Mold (Tap μ L f (Twang R a L Z x i) s) (Flair (V d e (P i)) k x a) ((c*c'+D*κ)*w'*Y*g) N n:=by
             let u:=Twang R a L Z x i; let v':= SX x x Z (orchestra (P i) a) (d:=d) (e:=e); have hz:BeamS (grain N m • (u-v')) (c'*w') (clockY x Z) (e+d):= mortPay x a i R hK hσ hΩ (h.fee.pulse m le_rfl) (hc m) hB; have h₁: Mold (Tap μ L f u s) (Tap μ L f v' s) (c*q*(c'*w')* Y) N n:=by
                   convert! payCut (μ:=μ) (m:=m) (p:=e+d) (u:=u) (v':=v') (Sumbond _ _ fun i _=> φBond ..) (cueBond ..) h hb hz (by positivity) hp using 1; rw [show e +d+ Mani (w+v) s=Rollup v w s d e from ?_]; rw [carveEq];unfold Rollup; omega -- see
             have h₂: Mold (Tap μ L f v' s) (Flair (V d e (P i)) k x a) (D*(w'*κ)*Visit r s*q) N n:= H E μ L Ω hΩ N Q Z a X b x h r hb (P i) _ (hp1 _) k (hQ.trans hx)
             apply (moldTrip h₁ h₂).trans; nlinarith only [mul_le_mul_of_nonneg_left hq (mul_nonneg (show 0≤ (c*c'+D*κ)*w' by positivity) hy)]
        rw [he]; refine ⟨Bins.falls _ fun i _=>hk i,?_⟩; rw [flairS k x a _ (fun i _=>hk i)]; apply (moldSum (s:=univ) (fun i _=> he' i)).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]; unfold Y g;ring
end YM.OPE.Libra.Shell
