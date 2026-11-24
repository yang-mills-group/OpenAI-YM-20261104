import YM.FormalBulk08.Sierra.Ahead

/-! Translate ot budget: use l1 over all slots rather than max, fixed rank.
Real-l1 evaluated at x in mesh units. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I X:Type}{u r:ℕ}{T:Tile (Biglot I) r}{B:ℝ}
def rayD (x:Track)(v:Cover):ℝ:=∑ i: Axis,|x i-(v i:ℝ)|
lemma ray_le (a:Cover)(v:Cover)(X:Track)(h:∀ i:Axis,|X i-(a i:ℝ)|≤3):
   rayD X v ≤ (size (v-a):ℝ)+12 ∧ ((size (v-a)):ℝ) ≤ rayD X v+12:= by
    have he i: (((v i-a i).natAbs:ℕ):ℝ)=|(v i:ℝ)-(a i:ℝ)|:= by rw [←Int.cast_sub,←Int.cast_abs,←Int.natCast_natAbs]; rw [Int.cast_natCast]
    unfold rayD size; simp_rw [Nat.cast_sum,Pi.sub_apply, he]; have hz : (12:ℝ)=∑ _i:Axis,(3:ℝ):= by simp [Axis]; norm_num
    rw [hz,← Finset.sum_add_distrib,←Finset.sum_add_distrib]; constructor
    · refine Finset.sum_le_sum fun i _=>?_ ; rw [show X i- _=(X i-(a i:ℝ))+ ((a i:ℝ)-v i) by ring]; apply (abs_add_le ..).trans; rw [abs_sub_comm ((a i):ℝ), add_comm _ |(v i:ℝ)-a i|]; exact add_le_add_right (h i) _
    apply Finset.sum_le_sum; intro i _; nth_rw 1 [show (v i:ℝ)-(a i:ℝ)= ((v i:ℝ)-X i)+(X i- (a i:ℝ)) by ring];apply (abs_add_le ..).trans;rw [abs_sub_comm (X i) (v i:ℝ)]; exact add_le_add_right (h i) _
def shellD (x:Track)(w:chain (Biglot I) r):= ∑ i, rayD x (w i).1
lemma icekit (a:Biglot I)(v:chain (Biglot I) r)(X:Track)(h:∀ i:Axis,|X i-(a.1 i:ℝ)| ≤3):
    shellD X v ≤ r* (herb (fame _) a v+12) ∧ (herb (fame _) a v:ℝ) ≤ shellD X v+12*r:= by
    let f:= fame I; let H:=herb f a v; let t i:= (size ((v i).1-a.1):ℝ)
    unfold shellD; have ht(i):t i ≤ H := Nat.cast_le.mpr (reached f (Fin.cons a v : chain (Biglot I) (r+1)) i.succ 0)
    have hv(i):= ray_le a.1 (v i).1 X h
    constructor
    · refine (Finset.sum_le_sum (fun i _=> (hv i).1.trans (add_le_add_left (ht i) _))).trans ?_; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; change _*(↑H+ (12:ℝ))≤ _; exact le_refl _
    apply le_trans (b:=∑ i,t i) _ ((Finset.sum_le_sum fun i _=>(hv i).2).trans (by rw [Finset.sum_add_distrib,Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm (r:ℝ)])); unfold t; rw [←Nat.cast_sum];apply Nat.cast_le.mpr; exact (show _ from Chapel.throne f a v)
variable {a:Biglot I}{x:Track}{ε:ℝ≥0}
lemma snow_eq (ε:ℝ≥0)(v:chain (Biglot I) r)(hb:ε≤1)(hx:∀ i, |x i-(a.1 i:ℝ)|≤3):
   (1+(ε:ℝ)*shellD x v)^u ≤ ((12*r+r+1:ℝ)^u*gauge u ε (herb (fame _) a v)) ∧ gauge u ε (herb (fame _) a v)≤ (12*r+1:ℝ)^u*(1+(ε:ℝ)*shellD x v)^u:= by
    unfold Sable.gauge; rw [←mul_pow,←mul_pow];let e:ℝ:=ε; have he:0≤e:= (ε).property;have h:e≤1:= show (ε:ℝ)≤1 from by exact_mod_cast hb
    let H:ℝ:= herb (fame _) a v; obtain ⟨ht,hv⟩:= icekit a v x hx; have hg : 0 ≤ shellD x v:= by unfold shellD rayD; positivity
    have yp:0≤ e*shellD x v:=mul_nonneg he hg; have hz:0≤e* H:=mul_nonneg he (Nat.cast_nonneg _); constructor
    · refine pow_le_pow_left₀ (add_nonneg zero_le_one yp) ?_ u
      change 1+e*_≤ (12*r+r+1)*(1+ e*H); have hK:e*shellD x v≤ r * (e*H)+ 12*(e*r):= by apply (mul_le_mul_of_nonneg_left ht he).trans; apply le_of_eq; unfold H;ring
      have hs:e* (r:ℝ)≤ r:=mul_le_of_le_one_left (Nat.cast_nonneg _) h; nlinarith only [hK,hs,hz,mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) hz,Nat.cast_nonneg (α:=ℝ) r]
    apply pow_le_pow_left₀ (by positivity); have hp:= mul_le_mul_of_nonneg_left hv he
    change e*H ≤ e*(shellD x v+12*r) at hp; change 1+e*H ≤ _
    have hs:e*(r:ℝ)≤ r:=mul_le_of_le_one_left (Nat.cast_nonneg _) h; change _≤ _ * (1+ e*shellD x v); nlinarith only [hp, yp,mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) yp, hs]
lemma joy (hp:ε ≤ 1)(hx:∀ i,|x i-(a.1 i:ℝ)| ≤ 3)(hv:Knoxville (grain (fame _) ε) (u:ℝ) a T B): SumBudget (fun v=>(1+ε* shellD x v)^u*‖T v‖) ((12*r+r+1:ℝ)^u* B):= by
   obtain ⟨hB,H,he⟩:=particle hv; let C:ℝ:=(12*r+r+1:ℝ)^u; have hC:0≤C:=by unfold C; positivity
   refine Spigot.sum_tier ⟨fun i=>mul_nonneg hC (mul_nonneg (gauge_low ..) (norm_nonneg _)), H.mul_left C, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he hC⟩ ?_ ?_
   · intro i; have h:0≤ shellD x i:=by unfold shellD rayD; positivity
     positivity
   intro i;rw [←mul_assoc C];exact mul_le_mul_of_nonneg_right (snow_eq ε i hp hx).1 (norm_nonneg _)
lemma bowtie (hp:ε ≤ 1)(hx:∀ i,|x i-(a.1 i:ℝ)| ≤3)(hv: SumBudget (fun v=>(1+ε*shellD x v)^u*‖T v‖) B): Knoxville (grain (fame _) ε) (u:ℝ) a T (Real.exp u*((12*r+1:ℝ)^u*B)):= by
   let C:ℝ:=(12*r+1:ℝ)^u;have hC:0≤C:=by unfold C;positivity
   have hh:=Spigot.sum_tier (g:=fun i=> C*((1+(ε:ℝ)*shellD x i)^u*‖T i‖)) (B:=C*B) (f:=fun i=> gauge u ε (herb (fame _) a i)*‖T i‖) ⟨fun i=>mul_nonneg hC (hv.1 i),hv.2.1.mul_left C,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hv.2.2 hC⟩ (fun i=>mul_nonneg (gauge_low ..) (norm_nonneg _)) (fun i=> le_trans (mul_le_mul_of_nonneg_right (snow_eq ε i hp hx).2 (norm_nonneg _)) (le_of_eq (mul_assoc ..)))
   exact back_grain (mul_nonneg hC ((tsum_nonneg hv.1).trans hv.2.2)) hh.2.1 hh.2.2
end YM.FormalBulk08.Sierra
