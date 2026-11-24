import YM.FormalBulk08.Dove.Ink

/-! Numerical convolution. Uniformity even moving ages. Registration doesn't
hide a value for position-dependent windows. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type} (S:Schedule) {θ:ℝ}
def sowing (i n:ℕ):ℝ:= S.scale n-S.scale i
lemma sowing_green (i n): n * Real.log (2:ℝ) ≤ sowing S i (i+n):= by
    induction n with
    | zero=> simp [sowing]
    | succ n ih=>
       have hp: Real.log (2:ℝ) ≤ Real.log ((S.block (i+n)).val:ℝ):= Real.log_le_log (by norm_num) (show (2:ℝ)≤_ by exact_mod_cast (by have :=S.block_large (i+n);omega : 2 ≤ (S.block (i+n)).val))
       unfold sowing at *;push_cast; rw [←add_assoc i n,Schedule.scale_succ]; linarith
lemma sowing_plus {i j}(h:i ≤ j): 0 ≤ sowing S i j:= by
    obtain ⟨n,rfl⟩:= Nat.exists_eq_add_of_le h; have hx:= sowing_green S i n; exact (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))).trans hx

def ringR (θ:ℝ)(m n:ℕ):ℝ:= Real.exp (-θ*sowing S m n)
lemma ring_fee (θ:ℝ)(m i k:ℕ): ringR S θ m i * ringR S θ i k= ringR S θ m k:= by unfold ringR; rw [←Real.exp_add]; unfold sowing; congr 1;ring
lemma ring_out (θ:ℝ)(m n): ringR S θ m n=ratioR S n m θ:= by
   unfold ringR sowing ratioR Schedule.scale; rw [Real.rpow_def_of_pos (div_pos (S.a_pos _) (S.a_pos _)), Real.log_div (S.a_pos _).ne' (S.a_pos _).ne', Real.log_inv,Real.log_inv]; congr 1; ring
lemma mulct_step (m): Mulct (S.block m)=ringR S (1/2:ℝ) m (m+1):= by
    unfold Mulct; rw [ring_out,ratioR,S.a_step,show S.a m/((S.block m).val:ℝ)/S.a m=((S.block m).val:ℝ)⁻¹ by field_simp [(S.a_pos _).ne'],←Real.sqrt_eq_rpow, Real.sqrt_inv]
lemma adjust_rate {θ : ℝ} (hx:θ≤ 1) (m N):
    ∃ Z:ℝ,0≤Z ∧ Z ≤ (S.block m).val ∧ ratioR S N (m+1) θ=Z*ratioR S N m θ := by
    let L:ℝ:=(S.block m).val; let W:=Real.exp (θ*Real.log L); have hp:1 ≤ L:= by unfold L;exact_mod_cast (show 1≤(S.block m).val from (S.block m).pos)
    have hw:0<W:=Real.exp_pos _; refine ⟨W,hw.le,?_ ,?_⟩
    · unfold W; refine le_trans (Real.exp_monotone (mul_le_mul_of_nonneg_right hx (Real.log_nonneg hp))) ?_; rw [one_mul,Real.exp_log (zero_lt_one.trans_le hp)]
    rw [←ring_out,←ring_out,ringR,ringR]; unfold W; rw [← Real.exp_add]; unfold sowing; rw [S.scale_succ]; unfold L; congr 1;ring
lemma adjusted (α θ:ℝ)(m N):
    ringR S α m (m+1)*ratioR S N (m+1) θ=ringR S (α-θ) m (m+1)*ratioR S N m θ:= by rw [←ring_out,←ring_out]; unfold ringR sowing; rw [← Real.exp_add,← Real.exp_add];congr 1;ring

structure Page (X:Type) where
   mesh : X→Schedule
   ell:X→ℕ
   age:X→Time ℕ
-- τ names
variable (P:Page X)
structure Leaf (P:Page X) where
   a:X
   b:ℕ
   zone:P.ell a ≤ b

def chron : Time (Leaf P) := ⟨fun x=> (P.age x.a).day x.b,fun x=>(P.age _).one x.b⟩
structure Years : Prop where
   /-- only older row, general ν/z/y accepted -/
   distance: ∃ B:ℝ,0≤B ∧ ∀ x n i, P.ell x ≤ i → i≤ n → (P.age x).day n≤B*((P.age x).day i + sowing (P.mesh x) i n)
   blocks: Soft (chron P) (fun i=>(((P.mesh i.a).block i.b).val:ℝ))

def stageFoot (x:Leaf P) (i:ℕ): Leaf P:= ⟨x.a,x.b+i,le_trans x.zone (Nat.le_add_right ..)⟩
lemma age_leg (h:Years P) (θ:ℝ)(ht:0<θ)(p:ℕ):
     ∃ M q:ℝ,0≤M∧0≤q∧q<1∧∀ (x:Leaf P)(j:ℕ), ringR (P.mesh x.a) θ x.b (x.b+j) * ((P.age x.a).day (x.b+j))^p ≤ M*((P.age x.a).day x.b)^p*q^j:= by
    obtain ⟨B,b,H⟩:= h.distance; obtain ⟨C,c,V⟩:= Cork.pockets p (show 0<θ/2 by positivity)
    let u:= θ/2;have hu:0<u:=by unfold u; positivity
    let z:= Real.log (2:ℝ); have hz:0<z:= Real.log_pos (by norm_num)
    refine ⟨B^p*C,Real.exp (-u*z),by positivity,(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr (by nlinarith),fun x j=>?_⟩
    let S:= P.mesh x.a;let T:= sowing S x.b (x.b+j);let a:= (P.age x.a).day x.b;let N:=(P.age x.a).day (x.b+j);have hp: j*z ≤ T:=sowing_green S _ _; have hT:0 ≤ T:= sowing_plus S (Nat.le_add_right ..); have hb:1≤ a:= (P.age _).one _; have ha:=zero_le_one.trans hb
    have hh : N≤ B*a*(1+T):= by
        refine (H x.a _ x.b x.zone (Nat.le_add_right ..)).trans ?_;rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ b;change a + T ≤ _;rw [mul_add,mul_one]; nlinarith only [hb,hT]
    change Real.exp (-θ*T)*N^p≤ _; have he : Real.exp (-θ*T)*Real.exp (u*T)≤ Real.exp (-u*z)^j:= by
        rw [←Real.exp_add,←Real.exp_nat_mul]; apply Real.exp_monotone; unfold u at *; nlinarith only [hp,ht]
    calc
       _ ≤ Real.exp (-θ*T)*(B*a*(1+T))^p:= by gcongr; exact (P.age _).good _
       _ = B^p*a^p*(Real.exp (-θ*T)*(1+T)^p):= by rw [mul_pow,mul_pow];ring
       _ ≤ B^p*a^p*(Real.exp (-θ*T)*(C*Real.exp (u*T))):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (V T hT) (Real.exp_pos _).le) (by positivity)
       _ = B^p*C*a^p*(Real.exp (-θ*T)*Real.exp (u*T)):= by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
end YM.FormalBulk08.Dove
