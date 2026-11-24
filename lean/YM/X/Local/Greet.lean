import YM.X.Local.Quay
/-!
# Drift and all-arity shrink for Crisp before gradient prices
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d :ℕ}{G:Gauge}{R r:ℝ}
local notation "e"=>epsilon q
local notation "L"=> (atTop:Filter ℕ)
local notation "K"=>Curly G
lemma motion {a b:ℤ}{f:Mist ℂ}(h:Visa q R a b f): (fun i=>f i 0)=O[L] (fun i=>(e i)^a):=by
   obtain ⟨C,hc,he⟩:= h.who; apply IsBigO.of_bound C; filter_upwards [he] with i hi; have ht:= e i; simpa only [Haze.price,day,Beamer.empty_road,Nat.cast_zero,add_zero,one_zpow,mul_one,Real.norm_of_nonneg (zpow_pos (epsilon_pos q _) _|>.le)] using! hi 0 (by simp [Beamer.empty_road])
include hq
lemma settles {a:ℤ}{f:ℕ→ℂ}(h:f=O[L] fun i=>e i^a)(ha:0<a): Tendsto f atTop (𝓝 0):= by
    refine h.trans_tendsto ?_; simp_rw [show ∀ i:ℕ,e i^a=e i^a.toNat from fun i=> by nth_rw 1 [show a= (a.toNat:ℤ) by omega]; rw [zpow_natCast]]; simpa only [zero_pow (show a.toNat≠0 from by omega)] using! (paths hq).cutoff.pow a.toNat
variable {A:ℕ→Brush G}{Q:Rich G}
lemma root_core (hr:R≥0)(h:Tide q r A)(he:R<r)(hp:Grasp Q)(ht: Fill (gate q r) (fun i=>e i^(d+1)) d 0 A (emerge q Q)){p:ℕ→Curly G}(hw:p∈Steady (Curly G)):
     Grove q R A Q d 0 (fun i _=>p i):= by apply Jar.read hq hr he h hp ht; have hz := jar_safe (R:=R) hq false hw; unfold gruel at hz; simp_rw [float_false] at hz; exact hz
lemma sample_root {p:ℕ→Curly G}(h:Grove q R A Q d k (fun i _=>p i)):
    (fun i=> e i ^(-(d:ℤ)) • (snap (A i) (p i)-shineP (emerge q Q i) d (p i)))=O[L] e:= by
    let v:= -(d:ℤ); have hx:=motion (Visa.asPow (c:=v) h.2); rw [show v+((d+1:ℕ):ℤ)=1 by omega] at hx; simp_rw [zpow_one] at hx; exact hx
variable (φ: Floor R)(P:Word G)
lemma shadow_drift (he:R<r)(h:Tide q r A)(hp:Grasp Q)(ht: Fill (gate q r) (fun i=>e i^(P.d+1)) P.d 0 A (emerge q Q)):
  Released (fun i=> e i ^(-(P.d:ℤ)) • (snap (A i) (warp q P φ i)-shineP (emerge q Q i) P.d (warp q P φ i))):= by
    have hx := (sample_root hq (root_core hq φ.positive.le h he hp ht (local_jar hq (bookMark P 1)))).trans_tendsto (show Tendsto e atTop (𝓝 0) from (paths hq).cutoff); let U(i:ℕ):= load q P i; refine Eq.mp ?_ (Released.sub ⟨0,hx⟩ (drift hq φ (ember_cost hq φ P he h hp ht))); congr 1; funext i; simp only [warp_embryo,map_sub,Pi.sub_apply,smul_sub]; abel
lemma root_tends (he:R<r)(h:Tide q r A)(hp:Grasp Q)(ht: Fill (gate q r) (fun i=>e i^(P.d+1)) P.d 0 A (emerge q Q)){x:Rich G}(hx:Grasp x)(hd:k≤P.d): Tendsto (fun i=> e i • clockLeaf (d:=P.d) k (x i) (warp q P φ i)) atTop (𝓝 0):= by
    have hh := Visa.asPow (c:=(1:ℤ)) (imprint (root_core hq φ.positive.le h he hp ht (local_jar hq (bookMark P 1))) hx hd); have h₀:= settles hq (motion hh) (by omega)
    simp_rw [zpow_one] at h₀; simp_rw [warp_embryo,map_sub,smul_sub]; exact (sub_zero (0:ℂ)) ▸ h₀.sub (hum hq φ (ember_cost hq φ P he h hp ht) hd hx)
lemma tube_le (hr:R≥0)(hr':R≤r)(h:Tide q r A):Tide q R A:= by
    refine ⟨h.kind,fun k f hf=> ?_,fun k f hf x hp z hz=> h.later k f hf x (hp.trans hr') z hz⟩; obtain ⟨c,hc,he⟩:= h.amounts k f hf; refine ⟨c,hc,he.mono (fun i hi z hz=>?_ )⟩; exact hi _ (hz.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hr' (amp_pos .. |>.le))))
lemma Grasp_cover (hr:r>0)(h:Tide q r A): ∃ Q:Rich G, Grasp Q∧ Fill (gate q r) (fun i=> e i^(d+1)) d 0 A (emerge q Q):= by
    let w i:= gate q r i; have hl : Tendsto w atTop atTop:= gate_asc hq r hr
    obtain ⟨B,p⟩:= replenish (n:=d) (m:=0) hl (h.ap d) h.kind; let Kw(k i:ℕ):= ((e i ^ (k+1))⁻¹ • B i k); let M:Rich G:= fun i j=>if j<d then Kw j i else 0; refine ⟨M,fun i=>?_,fun i hi=>?_⟩
    · unfold M; split_ifs with H; exact arm_eating hl (epsilon_pos q) (paths hq).cutoff p (fun k hk j l=> Tide.sends hq hr.le h l j) i H -- split in let?
      exact Released.zero
    have he(k i:ℕ)(h:i<d): (sauce (e k) (M k)) i=B k i:= by unfold M; rw [power_sauce,if_pos h]; unfold Kw; rw [smul_smul, mul_inv_cancel₀ (pow_pos (epsilon_pos q _) _|>.ne'),one_smul]
    have hv(k:ℕ): arm d (emerge q M k) = arm d (B k):= by unfold emerge; simp_rw [arm_point]; exact Finset.sum_congr rfl (fun i hi=>by rw [he k i (Finset.mem_range.mp hi)])
    simp_rw [hv]; exact p i hi
lemma pure_root {x:Rich G}(hx:Grasp x)(hd:k≤P.d) : Tendsto (fun i=> e i • clockLeaf (d:=P.d) k (x i) (warp q P φ i)) atTop (𝓝 0):= by
    obtain ⟨B,hB,h⟩:= Grasp_cover (d:=P.d) hq (show 0<R+1 from by linarith [φ.positive]) (Tide.empty (q:=q) (G:=G)); exact root_tends hq φ P (lt_add_one R) Tide.empty hB h hx hd
end YM.PositionX.Crystal
