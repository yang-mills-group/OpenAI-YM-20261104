import YM.FormalBulk08.Dove.Ore

/-! Enabled contraction, also may use for sources. Spare block powers
inserted one-time, not series powers. Θ fixed from Flat. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{P:Page X}{C:Pin P}{θ α:ℝ}
variable {V:Deck C→Type*}{r:ℕ}{T:(x:Deck C)→ Tile (V x) r}{R:∀ x,Reach (V x)}{σ:Deck C→ℝ}
lemma vanishing (h:Years P)(hp: θ < α)(hx:θ ≤ 1)(ht:Cost ((sage C).reach (peak C)) (fun x:X=>R (peak C x)) (fun x=> σ (peak C x)) (fun x=> T (peak C x))){K:Turn C→ℝ}(hk:Soft (tide C) K) (he:∀ x,0≤K x)(H:∀ (x:Turn C) B,Bail (R x.ups) (σ x.ups) (T x.ups) B→ Bail (R x.bed) (σ x.bed) (T x.bed) (Turn.rad α x*B+K x*Degree θ x.ups)):
    Dust (sage C) R σ (Degree θ) T := by
   obtain ⟨B,b,Y⟩:= ht
   let k (x:Turn C):ℝ:=((P.mesh x.a).block x.b).val; have hu:Soft (tide C) k:= h.blocks.reach (fun x:Turn C=>x.toLeaf)
   let f (x:Deck C)(Z:ℝ):Prop:= Bail (R x) (σ x) (T x) (Z*Degree θ x); have hv x:f (peak C x) (B x):= by
       have he: Degree θ (peak C x)=1:= by unfold Degree ratioR; rw [show (peak C x).a=x from rfl,show (peak C x).b=_ from (show (peak C x).b=C.N x from rfl), div_self ((P.mesh x).a_pos _).ne', Real.one_rpow];
       unfold f; rw [he,mul_one];exact Y x
   have he (x:Turn C)(Z:ℝ)(h:f x.ups Z)(_q:0≤Z): f x.bed (Turn.rad (α-θ) x * Z + K x*k x):= by
       obtain ⟨A,e,a,V⟩:= adjust_rate (P.mesh x.a) hx x.b (C.N x.a); apply (H x _ h).mono
       have h': Turn.rad α x*Degree θ x.ups= Turn.rad (α-θ) x* Degree θ x.bed:= adjusted _ _ _ _ _
       unfold f at *
       change _≤(Turn.rad (α-θ) x * Z + K x*k x)*Degree θ x.bed; rw [add_mul,mul_right_comm (Turn.rad _ x), h'.symm]; have hy : K x* A ≤ K x*k x:=mul_le_mul_of_nonneg_left a (he x)
       have heq:Turn.rad α x*(Z*Degree θ x.ups)=(Turn.rad α x*Degree θ x.ups)*Z:= by ring
       rw [heq, show K x*Degree θ x.ups= K x*A*Degree θ x.bed from (by rw [show Degree θ x.ups=A*Degree θ x.bed from V]; ring)]; exact add_le_add_right (mul_le_mul_of_nonneg_right hy (ratioR_pos ..).le) _
   exact upward h (sub_pos.mpr hp) (f:=f) (fun i _ hp _ hu=> hp.mono (mul_le_mul_of_nonneg_right hu (ratioR_pos ..).le)) b hv (hk.times hu) he
lemma actuality (h:Years P)(hp:0<α) (ht:Cost ((sage C).reach (peak C)) (fun x:X=> R (peak C x)) (fun x=> σ (peak C x)) (fun x=>T (peak C x))){K:Turn C→ℝ}(hk:Soft (tide C) K)(H:∀ (x:Turn C) B,Bail (R x.ups) (σ x.ups) (T x.ups) B→ Bail (R x.bed) (σ x.bed) (T x.bed) (Turn.rad α x*B + K x)):
    Cost (sage C) R σ T:= by
   obtain ⟨B,b,P⟩:= ht; obtain ⟨C,c,-,Q⟩:= upward h hp (f:=fun i a=> Bail (R i) (σ i) (T i) a) (fun i A hp B h=>hp.mono h) b P hk (fun i a h _=> H i a h); exact ⟨C,c,Q⟩
end YM.FormalBulk08.Dove
