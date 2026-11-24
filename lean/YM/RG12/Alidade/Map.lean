import YM.RG12.Alidade.Atlas
import YM.RG12.Rail.Dials -- slugg?
/-! # Select the strengthened travel card -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak Commission
open Pert.Dense Push.PriceCompiler
open scoped Topology BigOperators

variable {G:Gauge}{p:Sheet G}{w:Rolls p}{θ:Protection w}{D:Delays θ}{B:Bar D}
local notation "lim0"=> Real.log
variable (U V:Wait B){A:Levels G}(hV:Paid V A)
local notation "logs"=>A.clock.hatBeta
local notation "year"=>A.clock.J
local notation "step"=>A.S.a
-- available eventually at *all* k. f is either k or prior-stage.
include hV
def passcost (A:Levels G)(k:ℕ):=radar (A.clock.hatBeta k) (A.clock.J k)
lemma travels (H:G.Simple)(hc: ∀ j s,V.readyHere j≤ s → Thinner U j s ∧ Thinner U (j+1) s ∧ trial (B:=B) j s ≤ V.window j s):
    ∀ᶠ k:ℕ in atTop, ∃ f:ℕ, f≤k ∧ ((f=k) ∨ (A.clock.J f + 1=A.clock.J k)) ∧
      (∀ i,f < i→i ≤ k→ A.clock.J i=A.clock.J k) ∧ Interior U A f ∧
      A.S.a f/A.S.a k ≤ passcost A k:=by
   have hp : ∀ j s,V.readyHere j ≤ s→ Bound U j s ∧ Bound U (j+1) s ∧ trial (B:=B) j s ≤ V.window j s:=fun j s hj=> let h:=hc j s hj; ⟨h.1.toBound,h.2.1.toBound,h.2.2⟩
   filter_upwards [A.fits.deep.eventually_gt_atTop p.first] with k hk
   let j:= A.clock.J k-1
   have hj:A.clock.J k=j+1:=by unfold j; omega
   have hJ:p.first≤j:=by omega
   obtain ⟨d,hd,hh,Hh⟩:=old hV hj hJ
   obtain ⟨c,h1,h2,h3⟩:= hV.run j hJ
   let x:= A.S.scale k;let y:=A.S.scale c; let v:= V.window j y
   have hT:A.clock.J c=j:=h3 c (Nat.sub_le ..) (Nat.le_add_right ..)
   have hC:c<k:= by
      by_contra! he; have h:= A.fits.mono he; rw [hj,hT] at h; omega
   obtain ⟨-,hA,-⟩:=hc j y h1
   have hY:y ≤ x:= scale_mono A hC.le
   let s:=U.window (j+1) x
   have ht := hA.thins x hY
   change (s:ℝ)*wide w (j+1) ≤ _ at ht
   rcases lt_or_ge s (k-d) with hf|hf
   · refine ⟨k,le_rfl, Or.inl rfl,fun _ _ _=>by omega,?_,?_⟩
     · refine ⟨hj ▸ hA.early.trans hY, hj ▸ hf.le.trans (Nat.sub_le ..),?_⟩; rw [hj]; intro i hi h; exact Hh _ (by change k-s ≤ i at hi; omega) h
     rw [div_self (A.S.a_pos k).ne']; exact radar_big ((A.fits.delayed k).le) _
   have hz : c ≤ d:=by
      by_contra! hi; have hq:=Hh _ hi hC.le; omega
   refine ⟨d,hd.le,Or.inr (by omega),fun i hi hh'=> (Hh i hi hh').trans hj.symm,later H U V hV hp h1 h2 hz h3 hh,?_⟩
   have he: preHat B x= A.clock.hatBeta k:=by unfold preHat x Calendar.hatBeta; rw [hV.bar]
   have hx:= march hV d k (j+1) hd.le Hh
   rw [Stock.a_log,Stock.a_log,← Real.exp_sub,passcost,← he,hj]
   apply exp_monotone
   linarith only [hx,ht,mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.mpr hf) (wide_pos w (j+1)).le]

structure Beacon (A:Levels G)(f:ℕ→ℕ)(X:ℕ→Prop) : Prop where
   grows:Tendsto f atTop atTop
   valid : ∀ᶠ k:ℕ in atTop,f k ≤ k ∧ X (f k) ∧ (¬ X k → A.clock.J (f k)+1=A.clock.J k) ∧ A.S.a (f k)/A.S.a k ≤ passcost A k

omit hV V in
theorem insures (H:G.Simple)(h:Early U)(V:Wait B):∃ Q:Wait B, Thicker U Q ∧ Thicker V Q ∧ ∀ A:Levels G, Paid Q A→∃ f,Beacon A f (Interior U A):=by
   obtain ⟨Q,hA,hV,hB⟩:=permit U h H V
   refine ⟨Q,hA,hV,fun A hQ=>?_⟩
   obtain ⟨N,hn⟩:= eventually_atTop.mp (travels U Q hQ H hB)
   choose! f h1 h2 _ h4 h5 using fun k hk=>hn k hk
   have hT:Tendsto f atTop atTop:= tendsto_atTop.2 fun i=>by
       filter_upwards [eventually_ge_atTop N,A.fits.deep.eventually_gt_atTop (A.clock.J i+1),eventually_ge_atTop i] with k hk hx hf
       rcases h2 k hk with ht|ht
       · rwa [ht]
       by_contra! hf; have hF:= A.fits.mono hf.le
       omega
   exact ⟨f,hT,(eventually_ge_atTop N).mono fun k hk=> by
     refine ⟨h1 k hk, h4 k hk, fun hx => ?_,h5 k hk⟩
     rcases h2 k hk with ha|ha
     · exact (hx (ha ▸ h4 k hk)).elim
     exact ha⟩
omit hV in
lemma radar_smaller {x:ℝ}(h:1≤x)(i:ℕ):radar x i≤x:= by
   nth_rw 2 [← exp_log (zero_lt_one.trans_le h)] -- rewrites? occurrence x includes? test
   exact exp_monotone (mul_le_of_le_one_right (Real.log_nonneg h) (mite_le _))
def Slurry (A:Levels G):Prop:=∀ i, let r:= radar (A.clock.hatBeta i) (A.clock.J (i+1)); (A.S.block i).val ≤ r ∧ A.clock.monitor i ≤ r ∧ A.clock.monitor (i+1) ≤ passcost A (i+1)
-- test val coerced to real
omit hV U V in
theorem subsidy (S:Delays θ): ∃ S':Delays θ, DelayLe S S'∧∀ (S₀:Delays θ)(Y:Bar S₀)(V:Wait Y),DelayLe S' S₀ → ∀ A:Levels G,Paid V A→ G.Simple→ Slurry A:=by
   -- Threshold on pre-step hat (and follows at post-step hat)
   choose x hx using fun j=>eventually_atTop.mp (((radar_grows j).eventually_ge_atTop ((w.L j).val:ℝ)).and (YM.Vac.Numbers.cost 1 (mite j) (mite_pos j)))
   refine ⟨{S with betaEntry:= fun j=>max (S.betaEntry j) (x j)},⟨fun _=>le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun S₀ Y V h A hV hh i =>?_⟩
   let j:= A.clock.J (i+1); let b:=A.clock.hatBeta i
   have he: x j ≤ b:= (show x j ≤ max (S.betaEntry j) (x j) from le_max_right ..).trans ((h.beta j).trans (hV.pays i))
   have hf:b ≤ A.clock.hatBeta (i+1):=by unfold b Calendar.hatBeta; gcongr; exact (Gauge.slopeConstant_pos hh).le; exact Commission.scale_mono A (Nat.le_succ i)
   have hk(k:ℕ)(_ht:i ≤ k)(hr:x j ≤ A.clock.hatBeta k) : A.clock.monitor k ≤ radar (A.clock.hatBeta k) j:= by
      have hb:=zero_lt_one.trans (A.fits.delayed k)
      have hw: YM.Vac.Numbers.P (A.clock.hatBeta k)^ (1:ℝ)≤ (A.clock.hatBeta k)^(mite j):= (hx j _ hr).2
      rw [Real.rpow_one,Real.rpow_def_of_pos hb] at hw
      exact hw
   refine ⟨?_,hk i le_rfl he,hk _ (Nat.le_succ i) (he.trans hf)⟩
   change ((A.clock.schedule.block i).val:ℝ) ≤ _
   rw [← A.fits.sameFactor,hV.lengths]; exact (hx j b he).1
end YM.RG12.Alidade
