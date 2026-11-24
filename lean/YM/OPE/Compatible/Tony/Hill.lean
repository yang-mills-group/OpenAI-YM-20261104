import YM.OPE.Compatible.Song.Carp
/-!
# Exponential Sensors for *vacuum* at one arity. No estimates for labels
with spatial volume growing along perimeter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J X Y:Type*}{d m r k i:ℕ}{G:Gauge}
namespace Wool
variable {a b s K σ D:ℝ}
open Page
noncomputable abbrev salt (s:ℝ)(p:Page I r) :ℝ:= Real.exp (s*stamp p)
lemma saltRat (p:Page I r): 0 ≤ salt s p := (Real.exp_pos _).le
lemma sorgh (p:Page I r)(he:0 ≤ s): 1 ≤ salt s p:= Real.one_le_exp (mul_nonneg he (Nat.cast_nonneg _))
noncomputable abbrev Felt (p:Script I r)(s b:ℝ):Prop:= Sack (salt s) p b
lemma snug {p:Script I r}(h:Felt p s b)(he:a≤ s) : Felt p a b:= Sack.minor h (fun x=>saltRat x) (fun _=>Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) le_rfl
noncomputable abbrev cone (s:ℝ)(n:ℕ):ℝ:=s/2/ ((n:ℝ)+1)
lemma peak (s:ℝ)(n:ℕ)(h:0<s): 0 < cone s n:= by unfold cone; positivity
lemma nugget {n:ℕ}(t:Chant G n) {p:Page (Shade G) r} (hp:p∈rim t r)(hs:0≤ s):
       salt (cone s r) p≤ Real.exp (s/2)*Real.exp (s/2 * lawn t):=by
       unfold salt; rw [← Real.exp_add]; apply Real.exp_monotone; rw[show s/2+s/2*lawn t=(1+(lawn t:ℝ))*(s/2) from (by ring)]; let x:=s/2; have ht:x ≥0:=by unfold x;linarith
       have hx: (stamp p:ℝ) ≤ (1+(lawn t:ℝ))*((r:ℝ)+1):=(show (stamp p:ℝ) ≤ 1+r*(lawn t:ℝ) from by exact_mod_cast (rimS t p hp)).trans (by nlinarith only [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) (lawn t)])
       unfold cone; calc
            _ ≤ s/2/((r:ℝ)+1)*((1+(lawn t:ℝ))* ((r:ℝ)+1)) := mul_le_mul_of_nonneg_left hx (by positivity)
            _ =_:= by field_simp
-- from(coeff kit)
lemma spike_cost (G:Gauge)(n r:ℕ)(s D:ℝ)(hs:0<s)(hd:0≤D):∃ B:ℝ,0 ≤ B ∧∀ (p: Chant G n),moderateX p D→ Felt (coff p r) (cone s r) (B*Real.exp (s*lawn p)):=by
       obtain ⟨c,hc,H⟩:=coff_price G n r (s/2) D 0 (half_pos hs) hd; let a:=cone s r
       refine ⟨Real.exp (s/2)*c,mul_nonneg (Real.exp_pos _|>.le) hc,fun p hp=>?_⟩; have hT:=H p hp; let t:=Real.exp (s/2*lawn p); let f(i:Page (Shade G) r):= salt a i*‖coff p r i‖
       let Z:= Real.exp (s/2)*t; have he(i): f i ≤ Z*(figure 0 i*‖coff p r i‖):=by
            unfold f; by_cases hv:i∈rim p r; · rw [show figure 0 i=1 from pow_zero ..,one_mul]; apply mul_le_mul_of_nonneg_right (nugget p hv hs.le) (norm_nonneg _)
            rw [stair p hv,norm_zero,mul_zero,mul_zero,mul_zero]
       have hu:0≤Z:=mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
       apply budget_minor (f:=f) ?_ (fun i=> mul_nonneg (saltRat i) (norm_nonneg _)) he; exact ⟨fun i=>mul_nonneg hu (hT.1 i),hT.2.1.mul_left _,by rw [tsum_mul_left]; apply (mul_le_mul_of_nonneg_left hT.2.2 hu).trans_eq; change Z*(c*t)=_; rw [show Real.exp (s*lawn p)=t*t from (by unfold t; rw [← Real.exp_add]; congr 1; ring)]; unfold Z; ring⟩
lemma brief (G:Gauge)(s D:ℝ)(n r:ℕ)(hp:0<s)(hd:0≤D):∃ C:ℝ,0≤ C ∧∀ (A:I→ Chant G n)(x:I→ℝ) U, saturate A x s U→(∀ i,moderateX (A i) D)→ Felt (timbre A x r) (cone s r) (C*U):=by
       obtain ⟨B,H,hb⟩:= spike_cost G n r s D hp hd; refine ⟨B,H,fun A x U h hg=>?_⟩; have ht(i): Felt (x i • coff (A i) r) (cone s r) (B*(‖x i‖*Real.exp (s*lawn (A i)))):= (Sack.scale_line (hb _ (hg i)) (x i)).tips (by apply le_of_eq; ring)
       exact Sack.draws ht (show SumBudget (fun i=> _) (B*U) from ⟨fun i=>mul_nonneg H (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left h.2.2 H⟩) (fun p=>sorgh p (peak s r hp|>.le))
end Wool
end YM.OPE.Flume.Script
