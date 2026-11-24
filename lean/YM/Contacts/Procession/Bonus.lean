import YM.Contacts.Procession.Oryx
import YM.Contacts.Odor.Aroma
/-!
# Post & pre costs on this same path

Keep polynomial cost in e.Z. Used on any join horizon (pre-calibration of frames).
-/
noncomputable section
namespace YM.Contacts.Procession.Port
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales
set_option autoImplicit false
variable {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
abbrev rentCall (i:ℕ)(h:i<n): Theater G := Delight.opens e.a e.M (E n) e.Q x e.oga e.lamp _ h
structure Wealthy (P:ℕ→TableFee):Prop where
    launch (i N:ℕ)(h:i<N) : (rentCall e E x i h).Rich (e.ξ (i+1)) (e.haloSpan i) (e.Z i) (1+e.Z i) (P i)
lemma pays : ∃ p:ℕ→TableFee, Wealthy e E x p∧ Sales e p:= by
     choose a ha hA using fun i r=> ((e.rentLaw x E 3 le_rfl i r).law.1); let p (i:ℕ):TableFee:= fun r k=> a r k (i+1); refine ⟨p,⟨fun i n h=> ?_⟩, fun i j=>(ha i j).next⟩; let X':= (E n).heir i h; let W:= X'.V; have he:W=e.provisional E i n:= by rw [provisional,dif_pos h]
     have hu:= e.ensures E i n h; have hh:=e.shine_due E i (n:=n) h; let T:=e.incident x E (i+1) n; let A:= rentCall e E x i h; have H:A.spout= e.out E i n:= by change axisSky G (e.R i) (Origin.stretch _ _ G W) = _; rw [he]; rfl
     exact ⟨ (show Roof (e.ξ (i+1)) T (p i) from ⟨fun j r=> (hA j r (i+1) n h).weaken bath_terrace le_rfl⟩), mul_pos (by norm_num: (0:NNReal)<2) (e.ξ_pos i),e.reaches i, (show W.strip _ _ from he.symm ▸ hu.directory), (e.z_pos i).le, H.symm ▸ hh, le_add_of_nonneg_right (e.z_pos i).le ⟩
-- location qualification
lemma increasing (i:ℕ) : e.Z i ≤ e.Z (i+1) := by
    let H:= e.a.clock.hatBeta; change lush _ ≤ lush _; apply add_le_add_right; apply max_le_max (le_refl 0); refine Real.log_le_log (Real.log_pos (e.a.fits.delayed i)) (Real.log_le_log (zero_lt_one.trans (e.a.fits.delayed i)) ?_); unfold Calendar.hatBeta; exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono e.a.S).monotone (Nat.le_succ i)) (Gauge.slopeConstant_pos e.simple).le) _ -- locate
lemma luggage {b:ℝ}{z:Cover}(h:(size z:ℝ) ≤ b*(e.L i).val)(hb:0≤b): parcelY (e.ξ (i+1)) z ≤ Real.exp b:= by
     refine Real.exp_le_exp.mpr ?_; change (e.Z (i+1))⁻¹ * _ ≤ _; rw [mul_comm, ← div_eq_mul_inv,div_le_iff₀ (e.z_pos (i+1))]; exact h.trans (mul_le_mul_of_nonneg_left ((e.harbor i).trans (increasing e i)) hb)
lemma tackle {b:ℝ}{z:Cover}(h:(size z:ℝ) ≤ b*(e.L i).val)(hb:0≤b): stuff (e.haloSpan i) (e.ξ (i+1)) z ≤ Real.exp (4+b):= by
    rw [stuff,Real.exp_add]; refine mul_le_mul ?_ (luggage e h hb) (Real.exp_pos _).le (Real.exp_pos _).le; refine Real.exp_le_exp.mpr ?_; linarith only [show (e.haloSpan i:ℝ)≤1 from NNReal.coe_le_coe.mpr (e.tent i)]
lemma goes [Fintype ι]{F:Field ι (Node X)} {x:Node X} (k:ℕ)(i:ℕ)(h:Rest (terrain (e.haloSpan i) X) x F b) : Rest (bath (e.ξ i) k X) x F (e.xloose k i * b):= by
   let Q:=e.Z i; let W:= (e.ξ i:ℝ); let U:=Real.exp 1; let t:ℝ:=k.factorial; let v:=e.xloose k i
   have ht (r:ℝ)(hr:0≤r) : Real.exp (W*r)*(1+r)^k ≤ v*Real.exp ( (e.haloSpan i:ℝ)*r) := by
      have hu:W≤1:= NNReal.coe_le_coe.mpr (e.ξ_one _); have hp:0<W:= NNReal.coe_pos.mpr (e.ξ_pos _); have hf: 0<t:=by unfold t; positivity
      have hy:Q*W=1:= mul_inv_cancel₀ (e.z_pos i).ne'; have hz : 0 ≤ Q:= (e.z_pos i).le
      let A:=1+r; have hN:= Real.pow_div_factorial_le_exp (W*A) (mul_nonneg hp.le (add_nonneg zero_le_one hr)) k
      have he : Real.exp (W*A) ≤ U*Real.exp (W*r):= by unfold A; rw [mul_add,mul_one, Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu) (Real.exp_pos _).le
      calc
        _=Real.exp (W*r)* (Q^k * (W*A)^k):= by rw [←mul_pow, ← mul_assoc Q W A,hy,one_mul]
        _ ≤ Real.exp (W*r)*(Q^k*(U*Real.exp (W*r)*t)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ( (div_le_iff₀ hf).1 (hN.trans he)) (pow_nonneg hz _)) (Real.exp_pos _).le
        _ = _:= by rw [show (e.haloSpan i:ℝ)* r=W*r+W*r from (by unfold W haloSpan; push_cast; ring),Real.exp_add]; unfold v xloose t Q U; ring
   have hv: 0≤v:= (e.fair_loose k).bank _; let m:=terrain (e.haloSpan i) X; let l:=bath (e.ξ i) k X; have hs (x:Option ι→Node X): l.bill x ≤ v*m.bill x:= by
      have hb : 1≤ v:= by simpa using ht 0 le_rfl
      apply l.wide x (one_le_mul_of_one_le_of_one_le hb (m.one_bill _)); intro i j; exact (ht _ (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left (m.width x i j) hv)
   exact budget_mono (budget_scale hv h) (fun _=> mul_nonneg (norm_nonneg _) (fee_plus _)) (fun i=> (mul_le_mul_of_nonneg_left (show fee l x i ≤ v*fee m x i from hs _) (norm_nonneg _)).trans_eq (mul_left_comm ..))
lemma fair_pad {p q:ℕ→ Type}[∀ i,Fintype (p i)][∀ i,Fintype (q i)] (k:ℕ){a b:ℕ→ℝ}(hp:e.Fair fun i=>Fintype.card (p i))(hq:e.Fair fun i=>Fintype.card (q i))(h:e.Fair a)(ht:e.Fair b): e.Fair (fun i=> pads (p i) (q i) k (a i) (b i)):= ((hp.mul h).mul ht).mul ((hq.mul h).pow _)
-- presupplies polynomial powers even at unreached horizon.P*/Requests. Others need polynomial Calendar first.
def Preset (b:ℝ)(z:Cover)(i:ℕ):Prop:= (size z:ℝ) ≤ b*(e.L i).val -- multiplicative bookkeeping
lemma Manifest (e:Oasis G) (P:ℕ→TableFee)(hp:Sales e P)(K B i:ℕ) (d:ℝ)(hd:0≤d):
     e.Fair (fun a=> skies (Mixed G (e.R a)) (Dye G) (Fare.star e.Q (e.R a) e.a.clock.kernel (e.haloSpan a) (P a)) (1+e.Z a) (e.Z a) d (K+B) (i+1)):= by
    let F(a:ℕ):=e.Wd a; let L:= hp; have hx: Sales e (fun a=> stainCharge (F a) (Fare.star e.Q (e.R a) e.a.clock.kernel (e.haloSpan a) (P a)) d):= ?_ ; let U(a:ℕ):=Fintype.card (Option (F a)); have hU:e.Fair (fun i=> U i):= ?_; have h : Sales e (fun a=> Pulse.sky (levity (cardTime (F a) (e.Z a)) (stainCharge (F a) (Fare.star e.Q (e.R a) e.a.clock.kernel (e.haloSpan a) (P a)) d))) := Sales.sky (fun j=> Sales.heights (hU.mul e.fair_z) hx j)
    · exact fair_pad e _ (p:=fun i=> Option (F i)) hU (q:=fun _=> Option (Dye G)) (e.fair_const _ (Nat.cast_nonneg _)) ((e.fair_const 1 zero_le_one).add e.fair_z) (h (K+B) (i+1))
    · unfold U; simp_rw [Fintype.card_option,Nat.cast_add,Nat.cast_one]; exact e.cardHeight.add (e.fair_const 1 zero_le_one)
    · intro i j; have ht': e.Fair (fun i=>(Fintype.card (Option (e.Wd i)):ℝ)):= by simp_rw [Fintype.card_option,Nat.cast_add,Nat.cast_one]; exact e.cardHeight.add (e.fair_const 1 zero_le_one);
      exact Fair.add (fair_pad e _ (p:=F) e.cardHeight (q:=fun i=> Option (F i)) ht' (e.fair_const 1 zero_le_one) (term_cash (hp i j))) (e.fair_const d hd) -- indentation
lemma coil_rough (k p r l v:ℕ) (B:ℕ)(b:ℝ)(hb:0≤b)(hi:k ≤ B)(hh:p<B): e.Permit (fun i c=> ∀ N:ℕ,∀ h:i < N,∀ z:Cover,Preset e b z i→∀ F:Field (Fin k) (Node (Dye G)),∀ u:ℝ,Poem F →∀ y:Dye G, Rest (e.Bx l (i+1)) (0,y) F u → Rest (e.Bx r i) (0,y) ((rentCall e E x i h).spot B p F z v) (c*u)):= by
    obtain ⟨Q,hQ,hp⟩:= pays e E x; let K:= Manifest e Q hp B p v _ (Real.exp_pos (4+b)).le; refine ⟨_, (e.fair_loose r).mul ((e.fair_const _ (Nat.cast_nonneg (α:=ℝ) (v+1))).mul K),fun i n he z hz F u hF y hu=>?_⟩
    rw [mul_assoc]; exact goes e r i (donates (hQ.launch i n he) (e.reaches i) (hu.upto _ bath_terrace le_rfl) (tackle e hz hb) hF hh hi y v) -- arguments goes cost rearrange, field notation donates?
end YM.Contacts.Procession.Port
