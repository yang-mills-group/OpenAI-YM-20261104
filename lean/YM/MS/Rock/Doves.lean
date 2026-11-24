import YangMills.WilsonProof.NativeSupport.YM.MS.Rock.Claim
/-!
# Doves for kernel growth

Gamma-removed interpolation (Arc/Doves). PSC price with M required uniform
 in m (holds for compact multipliers, even Gram). Iterations t,z,l tested individually. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I E F H J:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
 {m n k:ℕ}{z:UScale I}{a b : I→ℝ}{r:ℝ}{f g:ℂ→Mob G} {u:ℂ→ Rip G}
variable {D:Set ℂ}{A B:ℝ}
def bn (z: Town): ℝ:= ‖(z:ℂ)‖
def mint (A:ℝ)(z:Town): ℝ:= LogMass A z
lemma mass_positive (i:Town)(h:0<A): 0<mint A i:= rpow_pos_of_pos h _
abbrev Shine (A:ℝ)(f:ℂ→Mob G): Prop:= fell bn (mint A) (fun i=> f i)
abbrev Sugar (A:ℝ)(u:ℂ→Rip G): Prop:= rib bn (mint A) (fun i=> u i)
-- use norm shapes satisfier
lemma compfits {α:ℂ→ ℂ}: scaleC bn (mint A) (fun i=>‖α i‖) ↔ Glow α A:= by
   have he (x:Town): (path bn).basic x=(1+‖(x:ℂ)‖):= by simp [Arc.path,bn]
   constructor <;> intro h <;> obtain ⟨C,hC,b,hb⟩:= h
   · refine ⟨C,hC,b,fun i hi=>?_⟩; simpa only [mint,Scale.strict,he] using hb (⟨i,hi⟩:Town) 0 (mem_univ _)
   exact ⟨C,hC,b,fun i p hp=> by simpa only [mint,Scale.strict,he] using hb i i.property⟩
lemma stars (h:Shine A f){l:Legs (Shore G n)}: Glow (fun i=>f i n l) A := by
    apply compfits.mp; obtain ⟨C,hC,b,hb⟩:= ride (h n ℝ (ray l)) 0; simp only [norm_iteratedFDeriv_zero] at hb; refine ⟨C*(1+‖(1:ℝ)‖)^b,mul_pos hC (by positivity),b,fun i p hp=> ?_⟩; specialize hb i 1; unfold fieldVal at hb; rw [ray_sail] at hb; apply hb.trans; dsimp only [Scale.strict,Arc.path]; rw [mul_pow, mul_comm ( (1+|bn i|)^b),mul_assoc C]; exact Eq.le (by ring)
-- instead compare numeric. Need scaleC closure operations via cost API.
structure Scout (f:ℂ→Mob G): Prop where
    price : ∃ A:ℝ,1≤A∧Shine A f
    sky : Hol Town f
structure TrackR (u:ℂ→ Rip G): Prop where
   price: ∃ A:ℝ,1≤A∧Sugar A u
   sky: Hop Town u
lemma two_wings {f g:ℂ→ℂ}(h:Clearing f)(hv: Clearing g) : Clearing (fun i=> f i+g i):= by
   obtain ⟨A,hA,hB⟩:= h.pay; obtain ⟨B,hP,H⟩:= hv.pay; let V := (path bn).strict fun _=> (Set.univ:Set ℝ)
   let L:=max A B; have hx : 1≤L:= le_max_of_le_left hA; have hm := compfits.mpr hB; have ht:= compfits.mpr H
   refine ⟨fun i hi=> (h.moss i hi).add (hv.moss i hi), L,hx, compfits.mp ?_⟩; apply Cost.Le.left ( (Cost.Le.right hm (u:=fun i _=> mint L i) (fun i p hp=> rpow_le_rpow (by linarith:0≤ A) (le_max_left ..) (show 0<2*((i:Town):ℂ).re + 1 from (i.property : ups _)).le)).add (Cost.Le.right ht (u:=fun i _=> mint L i) (fun i p hp=> rpow_le_rpow (by linarith:0≤B) (le_max_right ..) (show 0<2*((i:Town):ℂ).re + 1 from (i.property:ups _)).le)) (fun i p hp=> (mass_positive i (zero_lt_one.trans_le hx)).le)); exact fun i p hp=> norm_add_le ..
lemma static_w {f:ℂ→ℂ}(h: Clearing f)(c:ℂ): Clearing (fun i=> c*f i):= by
   obtain ⟨A,hA,C,hC,b,hb⟩:=h.pay; refine ⟨fun i hi=> (h.moss i hi).const_mul _, A,hA, C*(‖c‖+1),mul_pos hC (by positivity),b,fun i hi=>?_⟩; let Z:=LogMass A i; let V:= (1+‖i‖)^b; have hV:V≥0:=pow_nonneg (by positivity) _; have hZ:0≤ Z:= (mass_positive (A:=A) (⟨i,hi⟩:Town) (by linarith)).le; calc
      ‖c*f i‖ = ‖c‖*‖f i‖ := norm_mul ..
      _ ≤ ‖c‖*(C*V*Z):= mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _)
      _ ≤ _:= ?_
   change _≤ C*(‖c‖+1)*V*Z; rw [mul_add,mul_one,add_mul,add_mul]; nlinarith [mul_nonneg (mul_nonneg hC.le hV) hZ]
lemma zero_w : Clearing (fun _=> (0:ℂ)):= by
   refine ⟨fun _ _=>differentiableAt_const _,1,le_rfl,1,zero_lt_one,0,fun i hi=>?_⟩; simp [LogMass]
lemma Dove (h:Scout f)(i:ℕ)(l:Legs (Shore G i)): Clearing (fun z=> f z i l) := by obtain ⟨A,hA,hP⟩:=h.price; exact ⟨h.sky.top i l,A,hA, stars hP⟩
lemma Crow {f0:ℂ→J→ℂ}(h:∀ i:J,Clearing fun z=> f0 z i) (k:((J→ℂ)→ℂ))(hk:k∈ Heat.Centre J): Clearing (fun z=> k (f0 z)):= by
   refine Submodule.span_induction (p:=fun k _=> Clearing (fun z=> k (f0 z))) ?_ zero_w ?_ ?_ hk; rintro i ⟨j,rfl⟩; exact h j
   · intro v w Hv Hw hv hw; exact two_wings hv hw
   intro c v Hv hv; exact static_w hv c
lemma agree_w {f g:ℂ→ℂ}(h:Clearing f)(H: Clearing g)(hx:∀ᶠ n:ℕ in atTop, f n=g n): Set.EqOn f g Town := by
   have he(z:ℂ): f z + (-1:ℂ)*g z=f z - g z:=by ring
   have ht: ∀ᶠ n:ℕ in atTop,f n + (-1:ℂ)*g n=0:= hx.mono fun k h=> by rw [he,h,sub_self]
   intro t hp; exact sub_eq_zero.mp (by simpa only [he, Pi.zero_apply] using flourishing (two_wings h (static_w H (-1))) ht hp)
end YM.MS.Rock
