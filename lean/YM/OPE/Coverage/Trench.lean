import YM.OPE.Coverage.Curtain
/-!
## Calendar log mesh and dense weak-window layout
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Function Filter Set Lattice Wilson RG Next.Rank Bid Push.PriceCompiler Precision Supply Real
open scoped Topology
variable {G : Gauge} {X:Sheet G} {w:Rolls X} {D:Protection w} {T:Delays D}{Z:Bar T}(I:Wait Z) (A:Levels G)
set_option quotPrecheck false
local notation "J" => A.clock.J
local notation "Y" => A.S.scale
local notation "len" => fun j=>((w.L j).val:ℝ)

structure Loft:Prop where
  paid : Paid I A
  tail : ∀ᶠ i:ℕ in atTop,X.first < J i ∧ I.readyHere (J i) ≤ Y i ∧ exp (len (J i)) ≤ Y i
  aisles j (hj:X.first ≤ j) : ∃ k,round (Y k) ≤ k ∧ ∀m, k-round (Y k) ≤ m → m ≤ k → J m=j

variable {A I} (H:Loft I A)
include H
lemma len_log(j:ℕ): 1< len j ∧ 0<log (len j) ∧ log 2 ≤ log (len j):= by
   have h:= (w.large j).size
   have h : (2:ℝ) ≤ len j:=by change (2:ℝ) ≤ ((w.L j).val:ℕ); exact_mod_cast (by omega : 2 ≤ (w.L j).val)
   exact ⟨lt_of_lt_of_le one_lt_two h, log_pos (by linarith only [h]), log_le_log zero_lt_two h⟩

lemma run_len(i k j:ℕ) (h:k ≤ i) (he:∀m,k < m→m ≤ i→J m=j): Y i-Y k=(i-k:ℕ)*log (len j):=by
   have hv(u:ℕ)(h:k+u ≤ i) : Y (k+u)=Y k+ u*log (len j):=by
      induction u with
      | zero => simp
      | succ u ih =>
        have he:=he (k+u+1) (by omega) (by omega)
        rw [Nat.add_succ,A.S.scale_succ,← A.fits.sameFactor,he,(Loft.paid H).lengths,ih (by omega)]; push_cast; ring
   have hg:= hv (i-k) (by omega); rw [Nat.add_sub_cancel' h] at hg; linarith only [hg] -- need k+(i-k)=i

open Station Ship
local notation "Xhat" => fun k=>Ship.preHat Z (Y k)
lemma prices (hG:G.Simple): ∀ᶠ k in atTop,2 ≤ Xhat k ∧
    log (len (J k)) ≤ log (1+Y k) ∧ Vac.Numbers.P (Xhat k) ≤ Xhat k ∧ log (Xhat k) ≤ 2*log (1+Y k):=by
   have ht:= A.S.divergent
   have hkg:Tendsto Xhat atTop atTop := Filter.tendsto_atTop_add_const_left _ _ (ht.const_mul_atTop (Gauge.slopeConstant_pos hG))
   have hv := hkg.eventually (Vac.Numbers.cost 1 1 one_pos)
   filter_upwards [hkg.eventually_ge_atTop 2,H.tail,hv,ht.eventually_ge_atTop Z.value,ht.eventually_ge_atTop G.slopeConstant] with k h2 ht hp hu hd
   have hy : 0 < Y k := ((Gauge.slopeConstant_pos hG).trans_le hd)
   have hU : len (J k) ≤ 1+Y k:=by have hu:=add_one_le_exp (len (J k)); linarith only [hu,ht.2.2,hy]
   simp only [rpow_one] at hp
   refine ⟨h2,log_le_log (zero_lt_one.trans (len_log H (J k)).1) hU,hp,?_⟩
   rw [log_le_iff_le_exp (lt_of_lt_of_le zero_lt_two h2), show (2:ℝ)*log (1+Y k)=log (1+Y k)+log (1+Y k) from two_mul _, Real.exp_add,Real.exp_log (by linarith : 0<1+Y k), Ship.preHat]
   nlinarith only [mul_le_mul_of_nonneg_right hd hy.le,hu,hy]

omit H in
lemma wants_lo {u v:ℝ}(hu:1<u)(hv:1 ≤ v): (Station.want u v:ℕ)*log u ≤ log v + log u:=by
   unfold want
   have h:=Nat.ceil_lt_add_one (div_nonneg (log_nonneg hv) (log_pos hu).le)
   let t:=((Nat.ceil (log v/log u)):ℝ)
   exact (mul_le_mul_of_nonneg_right h.le (log_pos hu).le).trans_eq (by field_simp[(log_pos hu).ne'])

omit H
variable {H}
local notation "depth" => fun b k=>Ship.benchCost Z b (A.clock.J k) (A.S.scale k)
lemma depth_width (H:Loft I A) (hG:G.Simple)(b:ℝ)(hb:0 ≤ b): ∃ C:ℝ, 0<C ∧ ∀ᶠ k in atTop, (depth b k:ℕ)*log (len (J k)) ≤ C*log (1+Y k):=by
   let Q:=fun k=> (Nat.ceil (log (Xhat k)^2):ℝ)
   refine ⟨2*b+66,by linarith only [hb],?_⟩
   filter_upwards [prices H hG] with k hp
   let x := Xhat k
   let B := Q k
   let u := len (J k)
   have hβ : 0 < x:=zero_lt_two.trans_le hp.1
   have hlog:0 < log x:=log_pos (one_lt_two.trans_le hp.1)
   have hpQ : 1 ≤ B:= by
     change (1:ℝ) ≤ ((Nat.ceil (log x ^ 2)):ℕ); exact_mod_cast (Nat.succ_le_of_lt (Nat.ceil_pos.mpr (pow_pos hlog 2)))
   have hq : log x ≤ x:=log_le_self (le_of_lt hβ)
   have hb' : log B ≤ 3*log x:=by
     have hu:= Nat.ceil_lt_add_one (sq_nonneg (log x))
     change (B:ℝ) < log x ^ 2 + 1 at hu
     have ht:(log x)^2 ≤ x^2:=pow_le_pow_left₀ hlog.le hq _
     rw [log_le_iff_le_exp (zero_lt_one.trans_le hpQ)]
     rw [show (3:ℝ)*log x=log x+log x+log x from by ring,Real.exp_add,Real.exp_add, Real.exp_log hβ]
     nlinarith only [hu,ht,hp.1,sq_nonneg (x-2), mul_nonneg (show 0 ≤ x-2 from sub_nonneg.mpr hp.1) (sq_nonneg x)]
   have hw:0 < Vac.Numbers.P x:= Real.exp_pos _
   have he : 1 ≤ Vac.Numbers.P x ^ b * Vac.Numbers.P x ^(2:ℕ):=one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) hb) (one_le_pow₀ (Real.one_le_exp (sq_nonneg _)))
   have h₁:=wants_lo (len_log H (J k)).1 (one_le_pow₀ hpQ (n:=10))
   have h₂:=wants_lo (len_log H (J k)).1 he
   rw [Real.log_pow] at h₁
   rw [Real.log_mul (Real.rpow_pos_of_pos hw b).ne' (pow_ne_zero _ hw.ne'),Real.log_rpow hw,Real.log_pow] at h₂
   push_cast at h₁ h₂
   have h: log (Vac.Numbers.P x) ≤ log x:=Real.log_le_log hw hp.2.2.1
   rw [show benchCost Z b (A.clock.J k) (A.S.scale k)= want u (Vac.Numbers.P x ^ b*Vac.Numbers.P x ^(2:ℕ)) + want u (B^(10:ℕ)) from rfl, Nat.cast_add]
   linarith only [h₁,h₂,h,mul_le_mul_of_nonneg_right h hb,hb',hp.2.2.2, mul_le_mul_of_nonneg_right hp.2.2.2 hb,hp.2.1]


def stationReady (Z:Bar T)(A:Levels G) (b:ℝ)(k:ℕ):= Ship.benchCost Z b (A.clock.J k) (A.S.scale k) ≤ k ∧ ∀m, k-Ship.benchCost Z b (A.clock.J k) (A.S.scale k) ≤ m → m ≤ k → A.clock.J m=A.clock.J k
def frontier (A:Levels G) (i:ℕ):=Nat.find (show ∃m,A.clock.J m=A.clock.J i from ⟨i,rfl⟩)
local notation "seam" => frontier A
lemma seam_early (i:ℕ): seam i ≤ i:=Nat.find_min' (p:=fun l=>J l=J i) _ rfl
lemma seam_stable (i:ℕ): J (seam i)=J i:=Nat.find_spec (p:=fun l=> J l=J i) _
lemma seam_min {m i:ℕ}(h:J m=J i): seam i ≤ m:=Nat.find_min' (p:=fun l=>J l=J i) _ h
lemma maturity {z z' : ℕ→ℕ}(hy:Tendsto z atTop atTop)(he:∀ᶠ i in atTop,J (z i) = J (z' i)):Tendsto z' atTop atTop:=by
   intro u hu; obtain ⟨k,hk⟩:= eventually_atTop.mp (show ∀ᶠ z in atTop,z∈u from hu)
   change ∀ᶠ x in atTop,z' x∈ u
   filter_upwards [he,(A.fits.deep.comp hy).eventually_gt_atTop (J k)] with i hi ht
   change J k < J (z i) at ht
   exact hk _ ((lt_of_not_ge (fun h=> not_le_of_gt ht (hi.symm ▸ A.fits.mono h))).le)
-- prove tends another
lemma seam_late : Tendsto seam atTop atTop:=maturity tendsto_id (Eventually.of_forall fun i=>(seam_stable i).symm)

lemma log_speed(C:ℝ)(hC:0 < C): ∀ᶠ y:ℝ in atTop,C*log (1+y) ≤ log 2/2* Real.sqrt y ∧ log 2/2 * Real.sqrt y ≤ y/2:=by
     have ht:= (isLittleO_log_rpow_atTop (by linarith : (0:ℝ)<1/2)).bound (div_pos (log_pos (by linarith : (1:ℝ)<2)) (show 0<(4:ℝ)*C by linarith))
     filter_upwards [eventually_ge_atTop (2:ℝ),ht,Real.tendsto_sqrt_atTop.eventually_ge_atTop (log 2)] with y hy ht hq
     simp only [Real.norm_eq_abs,abs_of_pos (log_pos (one_lt_two.trans_le hy))] at ht
     change log y ≤ log 2/(4*C) * |y^(1/2:ℝ)| at ht
     rw [←Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at ht
     have hf: log (1+y) ≤ log y+log y:=(Real.log_le_iff_le_exp (by linarith)).mpr (by rw [Real.exp_add,Real.exp_log (zero_lt_two.trans_le hy)]; nlinarith only [hy,sq_nonneg (y-1)])
     have hi:log y ≤ log 2*Real.sqrt y/(4*C):= by rw [div_mul_eq_mul_div] at ht; exact ht
     constructor
     · linarith only [mul_le_mul_of_nonneg_left hf hC.le, (le_div_iff₀ (by positivity : (0:ℝ)<4*C)).mp hi]
     rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (by simpa only [Real.mul_self_sqrt (by linarith only [hy] : 0≤y)] using mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg y)) zero_le_two
variable (H: Loft I A)
include H

def terminal (A:Levels G)(i:ℕ):Prop:=∀ m,A.clock.J m=A.clock.J i → m ≤ i
lemma tail_permit (hG:G.Simple)(b:ℝ)(hb:0≤b): ∀ᶠ k in atTop, terminal A k → stationReady Z A b k:=by
    choose z h₁ h₂ using fun i:ℕ=> H.aisles (J i) (by rw [← H.paid.firstZero]; exact A.fits.mono (Nat.zero_le i))
    have he(i):J (z i)=J i:= h₂ i _ (Nat.sub_le ..) le_rfl
    have hz:= maturity (A:=A) (z':=z) tendsto_id (Eventually.of_forall fun i=>(he i).symm)
    obtain ⟨c,hc,hK⟩:= depth_width H hG b hb
    have hp:= A.S.divergent
    have h':= (hp.comp hz).eventually_gt_atTop 0
    filter_upwards [hp.eventually (log_speed _ hc),hK,h',H.tail] with k hq hB hp hG hlast
    have he₁:= he k; have ht := hlast (z k) he₁
    let b':=depth b k
    let s:= Y k; let t:=Y (z k); let L:=log (len (J k))
    have hL:0<L:=(len_log H (J k)).2.1
    have hp:0 < t:=hp
    have hJ {m}(hu:z k-round t ≤ m)(h:m ≤ k):J m=J k:= by
        by_cases h':m ≤ z k
        · exact h₂ k _ hu h'
        exact le_antisymm (A.fits.mono h) (he₁ ▸ A.fits.mono (le_of_not_ge h'))
    have hF:s-t = (k-z k:ℕ)*L:=run_len H k _ _ ht (fun m h h'=>hJ ((Nat.sub_le ..).trans h.le) h')
    have he':b' ≤ (k-z k)+round t:=by
         suffices h:(b':ℝ)≤(↑(k-z k+round t):ℝ) by exact_mod_cast h
         apply (le_of_mul_le_mul_right (α:=ℝ)) _ hL
         change (b':ℝ)*L ≤ _*L
         rw [Nat.cast_add,add_mul, ← (show s-t=↑(k-z k)*L from hF)]
         apply (show (b':ℝ)*L ≤ c*log (1+Y k) from hB).trans
         obtain hl|hl := le_total s (2*t)
         · have hh : sqrt s ≤ 2*sqrt t:= by nlinarith only [hl,Real.sq_sqrt hp.le,Real.sq_sqrt (show 0≤ s by dsimp only [s,t] at *; linarith only [hp,hF,Nat.cast_nonneg (α:=ℝ) (k-z k),mul_nonneg (Nat.cast_nonneg (α:=ℝ) (k-z k)) hL.le]),Real.sqrt_nonneg t]
           refine hq.1.trans ?_
           have hT : Real.sqrt t ≤ (round t:ℝ) := Nat.le_ceil _
           have hℓ:log 2 ≤ L:=(len_log H (J k)).2.2
           have h':=calc log 2/2*Real.sqrt s ≤ log 2*(round t:ℝ):=by have hf:=mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hT zero_le_two)) (le_refl (log 2)) (Real.log_pos one_lt_two).le (by positivity); linarith only [hf]
                         _ ≤ ↑(round t)*L:=(by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hℓ (Nat.cast_nonneg _))
           linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (k-z k)) hL.le,hF,h']
         refine (hq.1.trans hq.2).trans ?_
         linarith only [hl,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (round t)) hL.le]
    have h_k: round t ≤ z k:=h₁ k
    have hu:b' ≤ k:=by omega
    exact ⟨hu,fun m hm=> hJ (by change k-b' ≤ m at hm; omega)⟩
end YM.OPE.Coverage
