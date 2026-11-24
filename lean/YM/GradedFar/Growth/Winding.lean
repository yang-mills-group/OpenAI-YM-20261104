import YM.GradedFar.Growth.Store

/-!
# Pay the log chain
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

def packer (Q : Loft G I) (f : J → I) : Loft G J :=
    ⟨comap f Q.path,Q.r ∘ f,Q.C,Q.C0,Q.B,Q.B0,Q.nearing.comp tendsto_comap⟩
section
-- utility for any compact apertures along loft
variable (Q : Loft G I) {C : ℝ} {p : ℕ} {V : (i:I) → J → E} {S : I→Set J} [NormedAddCommGroup E]
-- for iteration errors here
variable {T : Type} {f:I→J→T}
abbrev Stays (S:I→Set J) := {t:I×J // t.2∈S t.1}
lemma extras (simple : G.Simple) (h : Bill ((packer Q (fun x : Stays S=> x.val.1)).board simple) p C (fun x=>V x.val.1 x.val.2)) :
    ∃ (W:I→ℝ), Bill (Q.board simple) p C W ∧ (∀ᶠ i in Q.path, 0 < W i) ∧
      ∀ᶠ i in Q.path, ∀ s∈S i, ‖V i s‖≤ W i := by
    obtain ⟨D,hD,k,h⟩:= h
    let W i:= D*(g (Q.r i))^p*post C (Q.height i) k
    have hv : ∀ᶠ i in Q.path, 0 < W i := by
      filter_upwards [Q.nearing.eventually (positive_g simple),(Q.climbs simple).eventually_ge_atTop 0] with i h hh
      unfold W post; positivity
    refine ⟨W,⟨D,hD,k,hv.mono fun i h=>(Real.norm_of_nonneg h.le).le⟩,hv,?_⟩
    exact (eventually_comap.mp h).mono fun i h s hs=> h ⟨(i,s),hs⟩ rfl
end

abbrev piled (Y : ℝ) := log (Y+4)/doubling
lemma unbroken (Y U : ℝ) (P : ℝ→ℝ) (c : ℝ) (hc : 0≤c) (hu : 0≤U) (hy : 1≤Y) (hp : P 0=0)
    (h : ∀ s∈ Icc 0 c, ∀ t∈Small, s+t≤c → P (s+t) ≤ (Y+3)*P s + U) :
    ∀ x∈ Icc 0 c, P x ≤ (Y+4)*exp (piled Y*c) * U := by
    let n := ⌈c/doubling⌉₊; let W:= Y+4; let V:= Icc 0 c
    have hw : 1≤ W:= by unfold W; linarith
    have hw':=lt_of_lt_of_le zero_lt_one hw
    have hA : 0≤Y+3:= by linarith
    have hd := doubling_pos
    have he (n : ℕ) (x : ℝ) (hh : x∈V) (hk : x≤ (n:ℝ)*doubling) : P x≤ W^n * U := by
      induction n generalizing x with
      | zero => simp only [Nat.cast_zero,zero_mul] at hk; rw [le_antisymm hk hh.1,hp,pow_zero,one_mul]; exact hu
      | succ n ih=>
        by_cases hx:x≤doubling
        · have hs:= h 0 (show 0∈V from ⟨le_rfl,hc⟩) x ⟨hh.1,hx⟩ (by rw [zero_add]; exact hh.2); rw [zero_add,hp,mul_zero,zero_add] at hs
          exact hs.trans (by have hy:= mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=n+1) hw) hu; rwa [one_mul] at hy)
        push Not at hx; let r:= x-doubling
        have hr : 0≤r:= sub_nonneg.mpr hx.le
        have hs : r∈ V :=⟨hr, (sub_le_self x hd.le).trans hh.2⟩
        have he : r+doubling=x:= by unfold r; ring
        have hi:= ih r hs (by rw [Nat.cast_add,Nat.cast_one] at hk; unfold r; linarith only [hk]); have ht:= h r hs doubling ⟨hd.le,le_rfl⟩ (he ▸ hh.2); rw [he] at ht
        have hh := mul_le_mul_of_nonneg_left hi hA; apply ht.trans; rw [pow_succ']; change _ ≤ (Y+4)*W^n * U
        nlinarith only [hh, hu, (one_le_pow₀ (n:=n) hw)]
    intro x hx
    apply le_trans (he n x hx (hx.2.trans ((div_le_iff₀ hd).1 (Nat.le_ceil _))))
    apply mul_le_mul_of_nonneg_right _ hu; unfold piled
    calc
      W^n = exp ((n:ℝ)*log W):= by rw [Real.exp_nat_mul, Real.exp_log hw']
      _ ≤ exp ((c/doubling+1)* log W) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg hc hd.le)|>.le) (log_nonneg hw))
      _ = (Y+4) * exp _ := by rw [show (c/doubling+1)*log W= log W + log W/doubling*c by ring, exp_add,exp_log hw']

private lemma both_loop {w A Y a D C s : ℝ} {E F R : ℝ → ℝ} (hw : 0≤w)
    (hs : s∈Icc 0 w) (ha : 1≤a) (hy : 1≤Y) (HC : 0<C) (HD : 0<D) (HA : 0<A)
    (he : ∀ s∈Icc 0 w,0≤ E s) (hf : ∀ s∈Icc 0 w,0≤F s) (h0:E 0=0) (h1:F 0=0)
    (hl : ∀ s∈Icc 0 w,R s ≤ C)
    (hp : ∀ s∈Icc 0 w, ∀ z∈Small, E (s+z) - 2*E s ≤ D)
    (hq : ∀ s∈Icc 0 w, ∀ z∈Small, F (s+z) - Y*F s - a*R s * E s ≤ A) :
    E s+ F s ≤ ((1+a*C)*D + A)*((Y+4)*exp (piled Y*w)) := by
    let k:=1+a*C; let T s:= k*E s+F s; let U:=k*D+A
    have ha':= lt_of_lt_of_le zero_lt_one ha
    have hy' : 1≤ k:= by unfold k; nlinarith only [HC,ha']
    have hy'' := zero_lt_one.trans_le hy'
    have hh:=unbroken Y U T w hw (by unfold U; positivity) hy (by unfold T; rw [h0,h1]; ring) (by
       intro s hs z hz hj
       have ht := mul_le_mul_of_nonneg_right (show a*R s ≤ k by unfold k; nlinarith only [hl s hs, ha']) (he s hs)
       unfold T U
       have kg:= mul_le_mul_of_nonneg_left (hp s hs z hz) hy''.le
       have ht' := mul_nonneg (show 0 ≤ Y*k by exact mul_nonneg (zero_lt_one.trans_le hy).le hy''.le) (he s hs)
       nlinarith only [hq s hs z hz,kg,ht,ht', hf s hs]) s hs
    have hk : E s ≤ k*E s:= by simpa only [one_mul] using mul_le_mul_of_nonneg_right hy' (he s hs)
    exact (add_le_add hk le_rfl).trans (hh.trans_eq (mul_comm ..))
private lemma max_norm {a b : ℝ} (h : ‖max a 0‖ ≤ b): a ≤ b :=
    (le_max_left ..).trans ((show _ ≤ ‖max a 0‖ from le_abs_self _).trans h)

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Q : Loft G I)
local notation "W"=> Q.board simple
lemma bill_stage (Y : ℝ) : Bill W 0 (-piled Y) (fun i=> exp (piled Y*Q.height i)) :=
   ⟨1,zero_lt_one,0, Eventually.of_forall fun i=> by unfold post; simp only [pow_zero,mul_one,one_mul,neg_neg]; exact (Real.norm_of_nonneg (exp_pos _|>.le)).le⟩

variable (Z : Coven G d) (θ : ℝ→ℝ) (ht : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1))
    (s : I → ℝ) (hs : Q.Mid s) (p : ℕ)
include H
lemma era_zero (r : ℝ) (hv : travels Z) : frame_err N M Z θ p r 0=0 := by
    simp_rw [frame_err,hv.1,crank,blend,names, neg_zero,zero_frame N M H,coeff_one]; rw [Finset.sum_eq_single 0]; · simp
    · intro b hb h; simp only [if_neg h,map_zero]; ext1 x; simp
    simp
lemma theta_zero (r : ℝ) (hp : 1≤p) : theta_err N M θ p r 0=0 := by
    unfold theta_err bend blend tells; rw [exp_zero, mul_one,neg_zero,zero_clock N M H, Finset.sum_eq_single 1]; · simp
    · intro b hb hx; simp [coeff_X,hx]
    intro h; simp at h; omega
include ht hs
-- entire accounting. Uses a costly T^fixed bound (buys it via increasing p)
local notation "vΔ"=>-(d:ℝ)+ -(d:ℝ)
set_option maxHeartbeats 300000 in
theorem chain (Y : ℝ) (hy : 1≤Y)
    (hq : Kind Z Y) (hv : travels Z) (h : PFrame N M Z θ p) (hp : 1≤p) (hb : PTheta N M θ p) :
    Bill W (p+1) (vΔ + -piled Y) (fun i=> theta_err N M θ p (Q.r i) (s i)+frame_err N M Z θ p (Q.r i) (s i)) := by
    let E i:= theta_err N M θ p (Q.r i); let F i:= frame_err N M Z θ p (Q.r i)
    let S (i:I):= (Icc 0 (Q.height i)) ×ˢ Small
    obtain ⟨a,ha,hp'⟩:= cranks_price N M H p d
    let Q' := packer Q (fun i:Stays S=> i.val.1); let x (i:Stays S):=i.val.2.1; let z (i:Stays S):=i.val.2.2
    have hX : Q'.Mid x:= Eventually.of_forall fun i=> i.property.1
    have hz : ∀ᶠ i in Q'.path, z i∈Small:= Eventually.of_forall fun i=> i.property.2
    have X : Q'.r = fun i=> Q.r i.val.1 := rfl
    have tol:=clock_iter N M H θ ht Q' x z hX hz p hp hb
    have dep:=frame_iter N M H Z θ ht Q' x z hX hz p Y a hp' hq hv h
    have meal:=crank_paid N M H Q' x hX _ (start_theta N M H θ ht Q') p d
    rw [X] at tol dep meal
    dsimp only [Q',x,z] at tol dep meal
    have p0:= extras Q (C:=0) (p:=p+1) (S:=S) (V:=fun i j=> max (leap_t N M θ p (Q.r i) j.1 j.2) 0) simple
    have p1:= extras Q (C:=-(d:ℝ) + -(d:ℝ)) (p:=p+1) (S:=S) (V:=fun i j=> max (leap_f N M Z θ p Y a (Q.r i) j.1 j.2) 0) simple
    have p2:= extras Q (C:=-(d:ℝ)) (p:=0) (S:=S) (V:=fun i j=> crank N M d j.1 p (θ (Q.r i):ℂ)) simple
    have tt:=p0 tol; have dd:=p1 dep; have mm:=p2 meal
    clear p0 p1 p2 tol dep meal X
    obtain ⟨D,hDT⟩:=tt; obtain ⟨A,hAT⟩:= dd; obtain ⟨M',hMT⟩:= mm
    let k i:= 1 + a * M' i; let U i:= k i*D i+A i
    have hx : vΔ ≤ -(d:ℝ):= by have := Nat.cast_nonneg (α:=ℝ) d; linarith
    have H0 : Bill W 0 vΔ k := ((no_cost W (1:ℝ)).mono_fee (by have hv : 0 ≤ (d:ℝ) := Nat.cast_nonneg _; linarith) le_rfl).plus
      ((product_fe W (no_cost W a) hMT.1).mono_fee (by linarith only [hx]) (Nat.zero_le _))
    have hh := product_fe W H0 hDT.1
    rw [Nat.zero_add,add_zero] at hh
    let V i:=U i*((Y+4)*exp (piled Y*Q.height i)); have he:= product_fe W (hh.plus hAT.1) (product_fe W (no_cost W (Y+4)) (bill_stage Q Y))
    rw [zero_add,zero_add, Nat.add_zero] at he
    refine he.of_le ?_
    filter_upwards [hs,hDT.2.2,hAT.2.2,hMT.2.2,hDT.2.1,hMT.2.1,hAT.2.1] with i hX hS hK hr HD HK HM
    let L:= Icc 0 (Q.height i)
    have hh:=both_loop (w:=Q.height i) (E:=E i) (F:=F i) (R:=fun s=> ‖crank N M d s p (θ (Q.r i):ℂ)‖) (le_trans hX.1 hX.2) (s:=s i) hX ha hy HK HD HM
      (fun x _=>norm_nonneg _) (fun x _=>norm_nonneg _) (theta_zero N M H θ p _ hp) (era_zero N M H Z θ p _ hv)
      (fun x h=>hr (x,0) ⟨h,(show 0∈Small from ⟨le_rfl,doubling_pos.le⟩)⟩) (fun x h z hz=>max_norm (hS (x,z) ⟨h,hz⟩))
      (fun x h z hz=>max_norm (hK (x,z) ⟨h,hz⟩))
    change ‖E i (s i)+ F i (s i)‖ ≤ ‖V i‖
    have hA : 0≤ E i (s i)+ F i (s i):= add_nonneg (show 0 ≤ E i _ from norm_nonneg _) (show 0 ≤ F i _ from norm_nonneg _)
    rw [Real.norm_of_nonneg hA, Real.norm_eq_abs]
    exact hh.trans (le_abs_self (V i))
end
end YM.FVA2.GradedFar.Growth
