import YM.Contacts.Prairie.Slip
import YM.Contacts.Prairie.Mine
import YM.Contacts.Barrage.Stakes
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
variable {k r d:ℕ}{S:Boom}
open Oasis
lemma owes (r k:ℕ){F:bore G}(h: Oasis.Amount e.x F 0): softRank (frock (r+2)) (dazzle F k (r+2)):= by
   obtain ⟨s,hs,T,hF⟩:= h.price; unfold dazzle; rw [if_pos (by omega)]; by_cases he:r≤2
   · interval_cases r
     · rw [show k+(0+2)-2=k by omega]; exact Lumen.salute e.simple e.x h.pure hF hs k (h.pinned k)
     · rw [show k+(1+2)-2=k+1 by omega]; exact (soften e.simple e.x h.pure hF hs k (h.pinned k)).1
     rw [show k+(2+2)-2=k+2 by omega]; exact (soften e.simple e.x h.pure hF hs k (h.pinned k)).2
   let Z:= F (k+(r+2)-2) (r+2); rw [show frock (r+2)=0 from by unfold frock; omega]; intro v; let V:= mask (G:=G) Z (Prod.snd ∘ v) (Prod.fst ∘ v); change Rays 0 (V ∘ axes); exact rays_zero ( (shadow_face _ _ (hF.shelter _ _) hs (Prod.snd ∘ v) (Prod.fst ∘ v)).analytic_real _)
def floorGoal (k h:ℕ):ℕ:=256 + Finset.sup (Finset.Iic h) (fun (r:ℕ)=> peak e.T G e.J e.J k (r+1)+2*(r+2))
lemma floorGain {L:Side}(h:(256:ℕ) ≤ L.val): Real.exp (-(Real.log (L.val:ℝ))/2) ≤ 1/4:= by
   have hh : 256 ≤ (L.val:ℝ):= by exact_mod_cast h
   apply le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : 0 ≤ (1:ℝ)/4); rw [← Real.exp_nat_mul]; push_cast; rw [show 2*(-Real.log (L.val:ℝ)/2)=-Real.log (L.val:ℝ) by ring, Real.exp_neg, Real.exp_log (side_pos _),← one_div]; apply (div_le_iff₀ (side_pos _)).mpr; nlinarith
variable {e} (T:e.License S ζ)(hk:3≤k)(hh:enough (e.floorGoal k d) S)(hs:s∈S) (hd:r≤d)
include T hk hh hs hd
lemma floor_cap : ∃ t≥(0:ℝ),∀ p (F:bore G)(i:ℕ), Oasis.Amount e.x F 0→∀ (a b), let n:=r+2; let X:= dazzle F i n; 0 ≤ b → Rooted (bath ζ k _) X a→(∀ j:ℕ, j<n → Rooted (terrain ζ _) (dazzle F i j) b) → Rooted (bath ζ k _) (e.Lift p s X) ((1/4 / e.coin k) * a + t*b):= by
   obtain ⟨v,hv,h⟩:= T.base s hs; let L:=s.L; let V:=e.flag s; have hl:= hh _ hs; have hz : peak e.T G e.J e.J k (r+1)+2*(r+2) ≤ L.val:= Nat.le_trans (Finset.le_sup (f:= fun r => peak e.T G e.J e.J k (r+1)+2*(r+2)) (Finset.mem_Iic.mpr hd)) ((Nat.le_add_left ..).trans hl); let d₁:= e.floorGoal k d; let n:= r+2; let Kh:ℝ:= e.coin k; have h':0<Kh := zero_lt_one.trans_le (e.coin_pos _)
   let κ:ℝ≥0:= 2*ζ; let u:= drops 1 n G (fun _=>1); let w:= max 0 u; let y:= e.tax; let d₂:=spanned V e.reach y; let P:= shipped κ L (Candles G) (Dye G) n d₂; let x:= (fit_spare κ ζ k T.emit_lt).choose; have hw:0≤w:= le_max_left ..; have hy:= e.tax_pos; have h₂:0≤d₂:= spanned_positive hy.le
   have ht : 0≤P:= by have he:= Real.exp_pos (2*(κ:ℝ)); unfold P shipped beamPrice; positivity
   have he:1≤x:= (fit_spare κ ζ k T.emit_lt).choose_spec.1
   have hL := side_pos L
   have hq:κ≤ e.reach:= by have ht:=T.warm; apply NNReal.coe_le_coe.mp; change 2*(κ:ℝ)≤ _ at ht; linarith only [ht,NNReal.coe_nonneg κ]
   have hx: ((2*(ζ:ℝ)/ L.val)* ((r+1:ℕ)+1:ℝ)) ≤ ζ:= by have hℓ:2*((r+1:ℕ)+1:ℝ) ≤ L.val:= (by push_cast at *; exact_mod_cast (show 2*(r+1+1) ≤ L.val from (Nat.le_add_left ..).trans hz)); rw [div_mul_eq_mul_div,div_le_iff₀ hL]; nlinarith only [hℓ,NNReal.coe_nonneg ζ]
   refine ⟨x*P*w,mul_nonneg (mul_nonneg (zero_le_one.trans he) ht) hw,fun p F i hf a b=>?_⟩; intro n' X hb hr hn; let R:= e.gas p s; have hT(l:List Axis)(h':l.length ≤ 3):= e.rod p s l (h'.trans (by have hh:=e.high; omega))
   have hl' : V.L.val≥ (censure e.T G e.J e.J k (r+1) hk (by omega)).choose:= by rw [Barrage.Reserve.peak,dif_pos ⟨hk,by omega⟩] at hz; exact le_trans (Nat.le_add_right ..) hz
   have hA:R.strip (e.reach:ℝ) e.tax := strip_mono (e.rod p s [] (Nat.zero_le _)) le_rfl (div_le_self hy.le (one_le_pow₀ (by exact_mod_cast s.L.property) )); -- args
   have hg:= h p; have hh: ζ ≤ 1:= T.down.trans T.thin; let Q j:= if j=n then a else b; have hX (j:ℕ)(hj:j≤ n): Rooted (terrain ζ _) (dazzle F i j) (Q j):= by unfold Q; split; subst j; exact hr.weaken bath_terrace le_rfl; next h=> apply hn; omega
   change Rooted _ (lifts (e.A p s) X) _
   let R':= lottery n' G (dazzle F i); have hR:= (lottery_due (n:=n') hh hn).weaken (fun _ => le_rfl) (show drops 1 n' G (fun _=>b) ≤ w*b from by refine le_trans (b:=u*b) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) hb); unfold u n'; unfold n drops; simp only [sum_mul,mul_one,mul_assoc]; exact le_rfl)
   have hG:= carpet (t:=e.reach) (B:=e.column p) (n:= r+1+1) (step_reserved s ζ) hh (e.awake p s) (e.wheel p s).governed hg.direct hv hA hq hy.le hg.feed hv hf.pure hX
   have hF:= roof_lift hR h₂ (succeeds hA hq hy.le) (step_reserved s ζ) -- P arg
   have hE:= (censure e.T G e.J e.J k (r+1) hk (by omega)).choose_spec ζ ζ L hl' s.odd T.light (show (ζ:ℝ)*2≤ e.T.α e.J from by rw [mul_comm]; exact NNReal.coe_le_coe.mpr hq) hx X R a (suited F hf.pure.my (r+1) i) (by unfold X dazzle; split; apply hf.pure.my.poem; apply Poem.empty) (e.owes r i hf) hr hT
   rw [show lifts (e.A p s) X=lifts (Origin.bleed G R) X-lifts (nest V G R) R' from hG]; refine (hE.sub (expand_fee (k:=k) T.emit_lt hF)).weaken (fun _=>le_rfl) (add_le_add ?_ ?_); · exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (floorGain (by exact le_trans (Nat.le_add_right ..) hl )) h'.le) hr.cash).trans_eq (mul_comm ..)
   exact le_of_eq (show x*(w*b*P)=x*P*w*b from by ring)
end Parcel
end
end YM.Contacts.Prairie
