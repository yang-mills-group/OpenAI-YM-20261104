import YM.OPE.Compatible.Cum.Sia
/-!
# Heat estimate before period. Launch once loath. Includes ext bounds all ratios chosen n-pol. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J: Type}{N:Side}[Fintype I]
variable {s:Finset J}[DecidableEq J]{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{X:J→Option (Site N)} {a b:Site N}{c y g κ σ l:ℝ}{Ω:Row I I}{C:ℕ→ℝ}{p e k d t n m h:ℕ}{F H:Curtain I}{r:J→ℝ}{x:deck I N}
lemma texDust : Texter v w s κ σ m n 0 e C I:=by
      refine ⟨0,le_rfl,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z a X c x h r he R b hB k hq; let A:=Vx (.some a) R (1:ℝ); let f:= SX x x Z A (d:=0) (e:=e); let q:= Script.value a R x
      have hp: SX x x Z (orchestra R a) (d:=0) (e:=e) = q • (1:E→ℝ):=by
           funext i; unfold SX q value; rw [scriptV a R _ (sootS hB),cueZ]; simp
      unfold Scripture; simp_rw [Hall_nil]; rw [hp,Tap_scale,penny]; by_cases hg:s=∅
      · have ht:e≤ k:=by simpa [Rollup,hg] using hq
        rw [if_pos hg, if_pos hg, throw_flair x ht,mul_one,zero_mul,zero_mul,zero_mul]; exact moldZero _ le_rfl
      rw [if_neg hg,if_neg hg,flair0 k x a,zero_mul,zero_mul,zero_mul,mul_zero]; exact moldZero _ le_rfl
lemma lux (hσ: 0<σ)(hκ:0≤κ)(hC:0 ≤ C) : n+HueS s ≤ m→ Texter v w s κ σ m n d e C I:=by
     apply inductS (fun s d e=> n+HueS s ≤ m → Texter v w s κ σ m n d e C I) (fun _ _ _=>texDust) _
     intro s d e hp hh hg hL; obtain ⟨b,hb,H⟩:= hp hL; obtain ⟨c,hc,K⟩:= swimming hC hκ hσ (fun i he=>hh i he e hL) hL
     choose! U hU H' using (fun i hi=>tryst (j:=i) (s:=s) (d:=d) (e:=e) hi rfl hC hκ hσ (fun k t=>hg i hi k t (by have h:=Finset.card_le_card (erase_subset i s); unfold HueS at *; omega)) hL) -- adjust
     let V:=∑ i∈s,U i; have hV:0≤ V:= sum_nonneg hU
     refine ⟨b+c+V,add_nonneg (add_nonneg hb hc) hV,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ N Q Z a X u x h r ha R q hR k ht; let Y:= LightX ∘ X; let t:= Shell.Hall Ω v w Q Y; let V'(i):= Vx (X i) (Q i) u; let P:= t s; let f:= Fig v w Q X u x Z; let T:=Shell.Temper e d R; let W:= WalkK Ω e d R P; let R'(i):=(if Y i then Once Ω (t (s.erase i)) e d R (w i) (v i) (Q i) else 0:Curtain I); have hP: P (d+1) e R=P d (e+1) T+W+ ∑ i∈s,R' i:= script_run ..
     have he:Rollup v w s (d+1) e=Rollup v w s d (e+1):=by unfold Rollup;omega
     have hy: SX x x Z (orchestra T a) (d:=d) (e:=e+1)=FTl e d (orchestra R a) x x x Z:=by
           ext i; unfold SX; erw [scriptV a T _ (sootS (StyleK m R hR)),tempered]; exact (scriptV a R _ (sootS hR)).symm
     let g(i):= Tap μ L f i s; let r₁ := g (FTl e d (orchestra R a) x x x Z); let r₂:= Urge (s:=s) μ L R a Z x f; let r₃(i):= Uric (s:=s) μ L R a Z x i f (V' i) (p:=v i) (n:=w i); have hr: g (SX x x Z (orchestra R a) (d:=d+1) (e:=e)) = r₁+r₂+∑ i∈s,r₃ i:= storyF μ L v w V' (orchestra R a) x x Z (Ferry Z) deltaH s (beryl Z) -- names
     let Hq:= Gates x s v w e (d+1); let A:=P d (e+1) T
     have h₁: Mold r₁ (Flair A k x a) (b*q* Visit r s*Hq) N n:=by
           have hs:= H E μ L Ω hΩ N Q Z a X u x h r ha T q (StyleK m R hR) k (he ▸ ht); change Mold _ _ _ _ _ at hs; change Mold (Tap μ L f (SX x x Z (orchestra T a) (d:=d) (e:=e+1)) s) _ _ _ _ at hs; rw [hy, ← he] at hs; exact hs
     have h₂:= K E μ L Ω hΩ N Q Z a X u x h r ha R q hR k ht; have h₃(i)(hi:i∈s): Bins (R' i) ∧ Mold (r₃ i) (Flair (R' i) k x a) (U i*q*Visit r s*Hq) N n:= H' i hi E μ L Ω hΩ N Q Z a X u x h r ha (Q i) (ha i hi) (h.alpha i hi) R q hR k ht; have hA: Bins A:= Hall_bins σ κ hΩ hσ hκ ha T (StyleK m _ hR); let L':=fun F:Curtain I=> Flair F k x a
     change Mold (g (SX x x Z (orchestra R a) (d:=d+1) (e:=e))) (Flair (P (d+1) e R) _ _ _) ((b+c+V)*q*Visit r s*Hq) N n; rw [hr,hP,flairA k x a (Bins.along hA h₂.1) (Bins.falls R' fun i hi=>(h₃ i hi).1),flairA k x a hA h₂.1, flairS k x a R' (fun i hi=>(h₃ i hi).1)]; refine (moldAdd (moldAdd h₁ h₂.2) (moldSum fun i hi=>(h₃ i hi).2)).trans_eq ?_; unfold V Hq; rw [←sum_mul,←sum_mul,←sum_mul];ring
end YM.OPE.Libra.Shell
