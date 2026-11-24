import YM.FormalOPE.RG10.Shutters.Dais
import YM.FormalOPE.RG10.Position.Columns
/-! Curvature parity of the normalized and the adjusted frames. Keep using the calibrated
coupling coordinate transformation in this symmetry. Condition on `train` and `warp` at e only
when solving for parity of the otherwise given mass-independent change. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
  RG10.Position RG10.Position.Grade Drivers
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d n:ℕ}(q:ℕ+){P:Plan F}
local notation "𝔭"=> PertExtension.Physical.Profile.n
local notation "ℳ" d => Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "w" d=> Deck.slots F d
local notation "g"=> rescale (-1:ℝ)

lemma onward (L:(ℳ 6)→fps) (h:snooze 𝔭 (w 6) L=L) : g (Peal.older F L)= -Peal.older F L := by
 have ht:= onOdd L h; let A:= Peal.mint F L; by_cases hh:IsUnit (coeff 1 A)
 · exact Triangle.rescale_inverse_odd ht hh
 unfold Peal.older; rw [Triangle.inverseScale,dif_neg hh]; simp

lemma shine (L:(ℳ 6)→fps) (h:snooze 𝔭 (w 6) L=L) (p:fps): g (Peal.Xaction F L p)=Peal.Xaction F L (g p):= by
 let B:=Peal.older F L; let x: fps:=(-1:ℝ) • X
 have he : ∀ p:fps,g p=subst x p:= rescale_eq_subst _; have hu:=Triangle.good B (Triangle.inverse_zero _); have hv:=Triangle.good x (by simp [x]); have hx : subst B x= -B:= by simp only [x, neg_smul,one_smul,← coe_substAlgHom hu,map_neg, coe_substAlgHom,subst_X hu];
 change g (Peal.Xaction F L p)=Peal.Xaction F L (g p); rw [Peal.action_on,Peal.action_on]; change g (subst B p)=_;
 rw [he,subst_comp_subst_apply hu hv,←he,show g B=-B from onward L h,hx.symm,←subst_comp_subst_apply hv hu,←he]

variable (h:Lantern P.stock)(H:Official P.stock)(hq:1<q.val)
include h H hq
lemma tint : ∀ᶠ m in atTop, snooze 𝔭 (w d) (Plan.collect F P q m d)= Plan.collect F P q m d:= by
 filter_upwards [dresses (d:=d) q h H hq,dresses (d:=6) q h H hq] with m he hv; unfold Plan.collect; apply (lamp ..).mpr; intro i; rw [shine _ hv, (lamp ..).mp he]; simp

omit hq H
variable {Y:Drivers}(Z:Patience P Y)
lemma phase : snooze 𝔭 (w d) (fun v:ℳ d=> Z.Yield v) = fun v:ℳ d=> Z.Yield v := by
 funext i; ext k:1
 let A(v:ℳ d):= Z.Yield v; let f q m:= Plan.collect F P q m d; let L:=(w d)
 have he : ∀ᶠ q in Y.ages, ∀ᶠ m in atTop,snooze 𝔭 L (f q m)=f q m:= Y.big.mono fun i hi=>tint (d:=d) i h Z.certified hi
 have hh (A: (ℳ d)→fps) : coeff k (snooze 𝔭 L A i) = lapse (S:=ℝ) k * (lapse (slots 𝔭 L i)*coeff k (A i)):= congr_fun (glance 𝔭 L A k) i
 rw [hh]
 obtain ⟨q,h',hk⟩:= he.and (Z.collected i k) |>.exists
 apply tendsto_nhds_unique ((hk.const_mul _).const_mul (lapse (S:=ℝ) k) |>.congr' ?_) hk
 filter_upwards [h'] with m hm; rw [show lapse k * (_ * _)= _ from (hh (f q m)).symm,hm]

-- temporal hypothesis on initial discrete frame gauge & flow only
omit h
section scale
variable {I:Type*}[DecidableEq I][Fintype I](w': I→ℕ)(A B:Matrix I I fps)(ρ:fps→+*fps)
omit [DecidableEq I] in
private lemma doze_mul : of (doze w' (A*B))=of (doze w' A) * of (doze w' B) := by
 ext i j : 1; simp only [Matrix.of_apply,doze,glass,mul_apply,map_mul,lapse,map_pow,map_neg,map_one,map_sum, mul_sum]; apply sum_congr rfl; intro k _; rw [pow_add,pow_add,pow_add];
 let I:=(-1:fps)^w' k
 have hI:I * I=1:= lap_twice (w' k);
 -- ring substitute
 linear_combination - ((-1:fps)^w' i*g (A i k) * ((-1:fps)^w' j * g (B k j))) * hI
omit [Fintype I] in
private lemma doze_one : of (doze w' (1:Matrix I I fps))= (1:Matrix I I fps):= by
 ext i j:1; by_cases h:i=j
 · subst i; simp [doze,glass,lapse,pow_add,lap_twice]
 simp [doze,glass,h]
omit [DecidableEq I] [Fintype I] in
private lemma doze_flow (h:∀ a:fps,g (ρ a)=ρ (g a)): of (doze w' (A.map ρ))=(of (doze w' A)).map ρ:= by ext i j:1; simp [doze,glass,lapse,h]
end scale
variable (R:Rails F)
local notation "𝔽" => Flow.warp R.flow 1
local notation "L"=> weight F d
local notation "w'"=> Deck.slots F d
structure Traced : Prop where
 odd : ∀ a:fps,g (𝔽 a)=𝔽 (g a)
 couched d : of (doze (Deck.slots F d) ((R.route d).train 1))=(R.route d).train 1

lemma shrubs (hk:Traced R) : of (doze w' (R.book d))= R.book d:= by
 let A:= R.route d; let u(S:Matrix (Deck F d) (Deck F d) fps):= of (doze w' S)
 have he (S) : u (RG10.Position.Grade.tile (Deck.price F d) S)= RG10.Position.Grade.tile (Deck.price F d) (u S):= by ext i j : 1; by_cases h:Deck.price F d i=Deck.price F d j <;> simp [RG10.Position.Grade.tile,doze,glass,u,h]
 have hv:= A.booked
 change u A.book=A.book; apply Passe.recovered A
 · intro i j h; simp [u,doze,glass,hv.1 _ _ h]
 · rw [← he,hv.2.1]; exact doze_one _
 unfold Passe.demand Retry.inter; apply sub_eq_zero.mpr
 have hz:= congr_arg u A.first_step; unfold u at hz; rw [doze_mul,doze_mul,doze_flow _ _ _ hk.odd, show of _=(A.train 1) from hk.couched d, show of (doze w' (A.drive 1))=_ from he (A.train 1)] at hz;
 rw [show u (A.train 1)=A.train 1 from hk.couched d] at hz; exact hz
include h
lemma decorated (hk:Traced R): snooze 𝔭 (w d) (R.adjust Z d)= R.adjust Z d:= by
 have he:= shrubs R hk (d:=d); unfold Rails.adjust; rw [← gaze_transition]; simp_rw [phase (d:=d) h Z]; congr 1
end YM.FormalOPE.RG10.Shutters
