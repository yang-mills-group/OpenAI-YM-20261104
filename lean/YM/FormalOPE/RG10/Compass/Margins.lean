import YM.Contact.JacobiAction
import YM.FormalOPE.RG10.Compass.Higher
/-! Center-specific signed turn of absolute position array on the inversion regulator. Finite
H-compare with a shifted box while keeping the frames fixed; cm sizes aren't omitted. Eventually
exact equality on *fixed* compact supports; lift asymmetry at boundary not a Taylor error. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Compass
open Function Wilson Lattice Gauge Precision Source PertExtension Filter RG PertExtension.LatticePT
  Finset RG10.Position InversionTop Orb LatticePT PowerSeries Chart Topology Metric Grid
open Maxwell Labels Plan Deck InversionWard FlatFeed
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {d n:ℕ} (q:ℕ+)(m:ℕ)(s:Signed)
local notation "r" => Ortho.move s.ortho
local notation "R" => Points.move s.ortho
local notation "T" => offsets q
local notation "N" => LatticePT.side q m
local notation "ε" => epsilon q m

def sunny : Equiv.Perm (Native q m) := ⟨s.act, s⁻¹.act,Signed.inv_act _, Signed.act_inv _⟩
def march : Equiv.Perm (T n m) := Equiv.piCongrRight fun _=> sunny q m s
lemma retreat (x:T n m) : march q m s⁻¹ (march q m s x)=x := (march q m s).symm_apply_apply _

lemma room {K:ℝ} (h: 2*K < LatticePT.period q m) (x:Native q m)(he: ‖point q m x‖≤ K) : point q m (s.act x) = r (point q m x):= by
 let A:=Lattice.lift x
 have he' : Lattice.lift (s.act x)=s.act A:=by
   rw [lift_eq_iff,← wrap_signed,show wrap _ A=x from wrap_lift _]; refine ⟨rfl,?_⟩; intro b; obtain ⟨a,rfl⟩:=s.perm.surjective b
   rw [Signed.act_at]
   have hf : 2* ↑|A a| < (((N).val:ℤ):ℝ):= by
     refine lt_of_mul_lt_mul_right  ?_ (epsilon_pos q m |>.le)
     push_cast; rw [mul_assoc, mul_comm _ ε]
     have h' := (PiLp.norm_apply_le (point q m x) a).trans he
     change ‖ε * (A a:ℝ)‖≤K at h'; rw [Real.norm_eq_abs,abs_mul,abs_of_pos (epsilon_pos ..)] at h'; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h' (by positivity)) h
   have hh:2*|A a| < ((N).val:ℤ):=by exact_mod_cast hf
   have ha:= le_abs_self (A a); have hb:= neg_le_abs (A a); split <;> omega
 unfold point; rw [he', Signed.ortho_move]; ext1 i; obtain ⟨i,rfl⟩:=s.perm.surjective i; change ε * (s.act A (s.perm i):ℤ)= s.act (WithLp.ofLp _) (s.perm i); simp only [Signed.act_at]; split <;> (first | simp only [Int.cast_neg,mul_neg] | skip) <;> rfl

lemma rangeWide (K:ℝ) (hq:1<q.val): ∀ᶠ m in atTop,K < period q m:= by
 have he : Tendsto (fun m=>K * (magnify q m^1 / (LatticePT.side q m).val)) atTop (𝓝 0):= by convert! (side_rate hq 1).const_mul K using 2; exact (mul_zero K).symm
 filter_upwards [he.eventually (gt_mem_nhds zero_lt_one)] with m hm
 rw [← mul_div_assoc,pow_one,div_lt_iff₀ (show 0<((LatticePT.side q m).val:ℝ) from Nat.cast_pos.mpr (LatticePT.side q m).pos),one_mul] at hm
 rw [LatticePT.period,epsilon, ← div_eq_mul_inv]; exact (lt_div_iff₀ (show 0 < magnify q m by unfold magnify; positivity)).mpr hm -- defeq period differs

lemma sampledRoom (K:ℝ)(hq:1<q.val): ∀ᶠ m in atTop, ∀ x:T n m, ‖Grid.sample q m x‖ ≤ K → Grid.sample q m (march q m s x)= R (Grid.sample q m x) := by
 filter_upwards [rangeWide q (2*K) hq] with m hm x hx; ext1 i; exact room q m s hm (x i) ((PiLp.norm_apply_le (Grid.sample q m x) i).trans hx)

open Contacts
variable (t:Test n)
private lemma sights : tsupport (t ∘ (moveList s.ortho).symm) = (moveList s.ortho) '' tsupport t := by
 rw [show tsupport (t ∘ (moveList s.ortho).symm) = (moveList s.ortho).symm ⁻¹' _ from tsupport_comp_eq_preimage t (moveList s.ortho).symm.toHomeomorph]
 ext i; constructor; intro h; exact ⟨_,h,(moveList s.ortho).apply_symm_apply _⟩; rintro ⟨i,hi,rfl⟩; simpa only [Set.mem_preimage,LinearIsometryEquiv.symm_apply_apply]

def tilted : Test n:= ⟨t ∘ (moveList s.ortho).symm,t.contDiff.comp (moveList (n:=n) s.ortho).symm.toContinuousLinearEquiv.contDiff, by rw [HasCompactSupport,sights]; exact t.hasCompactSupport.image (moveList s.ortho).continuous, fun x hx=>by rw [sights] at hx; obtain ⟨x,hx,rfl⟩:=hx; exact Points.move_in _ (t.tsupport_subset hx)⟩
lemma under (x:Points n):tilted s t (R x)= t x:= congr_arg (fun i=> t i) ((moveList s.ortho).symm_apply_apply x)
private lemma horizon (f:Test n) : ∃ K:ℝ, ∀ x:Points n, f x≠0→‖x‖≤K:= by
 obtain ⟨K,hK⟩:= f.hasCompactSupport.isBounded.subset_closedBall (0:Points n)
 exact ⟨K,fun x hx=> show _ from by simpa only [mem_closedBall,dist_zero_right] using hK (subset_closure (show x∈support f from hx))⟩
lemma collision (hq:1<q.val): ∀ᶠ m in atTop, ∀ x:T n m, tilted s t (Grid.sample q m (march q m s x))= t (Grid.sample q m x) := by
 obtain ⟨k,hk⟩:= horizon t; obtain ⟨p,hp⟩:= horizon (tilted s t)
 filter_upwards [sampledRoom (n:=n) q s k hq,sampledRoom (n:=n) q s⁻¹ p hq] with m hk' hp' x; by_cases h:t (Grid.sample q m x)=0
 · by_cases w: tilted s t (Grid.sample q m (march q m s x))=0
   · rw [h,w]
   have he:= hp' (march q m s x) (hp _ w); rw [retreat] at he; nth_rw 1 [he] -- dangerous occurrences; sample(march) no
   rw [show s⁻¹.ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s]; rfl
 rw [hk' x (hk _ h),under]
end YM.FormalOPE.RG10.Compass
