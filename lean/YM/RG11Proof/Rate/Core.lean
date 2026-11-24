import YM.RG11Proof.Formal.Orbit

/-!
# Common small regulator budget

Scalar real estimates `O(E)` and `O(1)` on one common Filter of regulator
inputs. All closure operations here are only fixed, finite demand, so their
existential constants & tail threshold may depend on all finite inputs/support
and horizon/order. Do NOT use theses lemmas on a growing number of fields,
arities, order, scales etc unless explicitly bounded uniformly (cost charged
outside the solver). For power/polylog schedules pay/retain `E` explicitly.
This development has nothing to do with Cauchy analytic-coupling estimates or
convergence of a formal series at a nonzero coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rate
open Filter
open scoped Topology BigOperators Classical
variable {α : Type*}

/-- If uniforms are required in volume, phase etc use FORALL constants in
the input predicates (e.g. filter comap of the actual schedule index,
INCLUDING all those cases in α). Passing to a single-volume subsequence instead
would give a different assertion. Choose E explicitly (e.g. spacing positive
power times log polynomial); possibly after finitely many slack reductions.
`NeBot` needed only for arguments which use the estimates to deduce an identity.
-/
structure Budget (α : Type*) where
  along : Filter α
  E : α→ℝ
  gone : Tendsto E along (𝓝 0)
  currency : ∀ᶠ a in along, 0 ≤ E a

-- Write the equivalent of =O via explicit tail invoices; we need analogous
-- err*(1+...) predicates involving UNKNOWN current-order entries, for which
-- relative errors are not appropriate. `NearFn` allows estimates against
-- another regulator variable.
def NearFn (k : Budget α) (f g : α→ℝ) := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in k.along, |f a - g a| ≤ C * k.E a
def Near (k : Budget α) (f : α→ℝ) (x : ℝ) := NearFn k f (fun _=> x)
def Bounded (k : Budget α) (f : α→ℝ) := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in k.along, |f a| ≤ C

variable {k : Budget α} {f g h u : α→ℝ} {x y : ℝ}
namespace NearFn
@[refl] theorem refl (f : α→ℝ) : NearFn k f f := ⟨0,le_rfl,Eventually.of_forall (by simp)⟩
@[symm] theorem symm (H : NearFn k f g) : NearFn k g f := by simpa only [NearFn,abs_sub_comm] using H

theorem trans (H : NearFn k f g) (H' : NearFn k g h) : NearFn k f h := by
  obtain ⟨C,hc,h⟩:=H; obtain ⟨D,hd,w⟩:=H'
  refine ⟨C+D,by linarith,?_⟩
  filter_upwards [h,w] with a ha hw
  rw [add_mul]
  exact le_trans (abs_sub_le _ _ _) (add_le_add ha hw)

theorem add (H : NearFn k f u) (hG : NearFn k g h) : NearFn k (fun a=>f a+g a) (fun a=>u a+h a) := by
  obtain ⟨C,hc,hX⟩:=H; obtain ⟨D,hd,w⟩:=hG
  refine ⟨C+D,by linarith,?_⟩; filter_upwards [hX,w] with a ha hw
  rw [add_mul,show f a+g a - (_+_)= f a-u a+(g a-h a) by abel]
  exact le_trans (abs_add_le ..) (add_le_add ha hw)

theorem neg (H : NearFn k f g) : NearFn k (fun a=> -f a) (fun a=> -g a) := by
  unfold NearFn; simp_rw [← neg_sub',abs_neg] -- neg_sub' ?
  exact H

theorem sub (H : NearFn k f u) (hG : NearFn k g h) : NearFn k (fun a=>f a-g a) (fun a=>u a-h a) := by
  simp_rw [sub_eq_add_neg]; exact H.add hG.neg

-- need ONE end for each factor, not convergence hypotheses on the whole expression.
theorem mul (H : NearFn k f u) (G : NearFn k g h) (F : Bounded k f) (W : Bounded k h) :
    NearFn k (fun a=> f a*g a) (fun a=>u a*h a) := by
  obtain ⟨L,hL,hLo⟩:=H; obtain ⟨P,hP,hPo⟩:=G
  obtain ⟨C,hC,hCo⟩:=F; obtain ⟨D,hD,hDo⟩:=W
  refine ⟨C*P+L*D,by positivity,?_⟩
  filter_upwards [hLo,hPo,hCo,hDo,k.currency] with a hLw hPw hCw hDw hE
  rw [show f a*g a-u a*h a=f a*(g a-h a)+(f a-u a)*h a by ring]
  apply le_trans (abs_add_le ..); simp_rw [abs_mul]
  calc
    |f a| * |g a-h a| + |f a-u a| * |h a| ≤ C*(P*k.E a)+(L*k.E a)*D := add_le_add
      (mul_le_mul hCw hPw (by positivity) hC) (mul_le_mul hLw hDw (by positivity) (by positivity))
    _ = _ := by ring

theorem turnsNear (h : NearFn k f g) (H : Near k g x) : Near k f x := trans h H

theorem compare_bound (H : NearFn k g f) (B : Bounded k f) : Bounded k g := by
  obtain ⟨C,hc,h⟩:=B; obtain ⟨L,hl,kA⟩:=H
  refine ⟨C+L,by positivity,?_⟩
  filter_upwards [h,kA,k.gone.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with a ha hh he
  calc |g a| = |g a-f a+f a| := by rw [sub_add_cancel]
       _ ≤ |g a-f a|+|f a|:= abs_add_le ..
       _ ≤ C+L:= by nlinarith [show k.E a < 1 from he]

theorem tendsto (h : NearFn k f g) (he : Tendsto g k.along (𝓝 x)) : Tendsto f k.along (𝓝 x) := by
  obtain ⟨C,-,hc⟩:=h
  have h : Tendsto (fun a=> f a-g a) k.along (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun _=> abs_nonneg _)) hc
    simpa using (k.gone.const_mul C)
  simpa only [sub_add_cancel,zero_add] using h.add he

theorem inv (h : NearFn k f g) (B : Bounded k (fun a=> (f a)⁻¹)) (C : Bounded k (fun a=> (g a)⁻¹))
    (H : ∀ᶠ a in k.along, f a≠0 ∧ g a≠0) : NearFn k (fun a=> (f a)⁻¹) (fun a=> (g a)⁻¹) := by
  obtain ⟨M,hM,hB⟩:=B; obtain ⟨N,hN,hC⟩:=C; obtain ⟨L,hL,h⟩:=h
  refine ⟨M*N*L,by positivity,?_⟩; filter_upwards [h,hB,hC,H,k.currency] with a ha hb hc hA hk
  obtain ⟨hu,hv⟩:=hA
  dsimp only at *
  rw [show (f a)⁻¹ - (g a)⁻¹ = (f a)⁻¹*(g a)⁻¹ * (-(f a-g a)) by field_simp; rw [neg_sub]]
  simp only [abs_mul,abs_inv,abs_neg] at hb hc ⊢
  rw [mul_assoc (M*N)]
  exact mul_le_mul (mul_le_mul hb hc (by positivity) hM) ha (by positivity) (by positivity)

theorem congr (H : NearFn k f g) (hf : u =ᶠ[k.along] f) (hg : h =ᶠ[k.along] g) : NearFn k u h := by
  obtain ⟨C,hc,ho⟩:=H; refine ⟨C,hc,?_⟩
  filter_upwards [hf,hg,ho] with a hw hj hx; simpa only [hw,hj]
end NearFn

namespace Bounded
@[simp] theorem const (c : ℝ) : Bounded k (fun _ => c) := ⟨|c|,by positivity,Eventually.of_forall fun _=>le_rfl⟩
theorem mul (h : Bounded k f) (H : Bounded k g) : Bounded k (fun a=> f a * g a) := by
  obtain ⟨X,hX,h⟩:=h; obtain ⟨Y,hY,H⟩:=H
  refine ⟨X*Y,by positivity,?_⟩; filter_upwards [h,H] with a h H
  rw [abs_mul]; gcongr

theorem add (h : Bounded k f) (H : Bounded k g) : Bounded k (fun a=> f a+g a) := by
  obtain ⟨X,hX,h⟩:=h; obtain ⟨Y,hY,H⟩:=H
  refine ⟨X+Y,by positivity,?_⟩; filter_upwards [h,H] with a h H
  exact (abs_add_le ..).trans (add_le_add h H)

theorem neg (h : Bounded k f) : Bounded k (fun a=> -f a) := by simpa [Bounded] using h

theorem sub (h : Bounded k f) (H : Bounded k g) : Bounded k (fun a=> f a-g a) := by simp_rw [sub_eq_add_neg]; exact h.add H.neg

theorem dominate (h : Bounded k f) (he : ∀ᶠ a in k.along, |g a| ≤ |f a|) : Bounded k g := by
  obtain ⟨C,hc,H⟩:=h; exact ⟨C,hc,(he.and H).mono fun _ ⟨hi,hj⟩=>hi.trans hj⟩
end Bounded

namespace Near
@[simp] theorem const (x:ℝ) : Near k (fun _=> x) x := NearFn.refl _
theorem bounded (h : Near k f x) : Bounded k f := NearFn.compare_bound h (Bounded.const _)
theorem add (H : Near k f x) (G : Near k g y) : Near k (fun a=>f a+g a) (x+y) := NearFn.add H G
theorem mul (H : Near k f x) (G : Near k g y) : Near k (fun a=>f a*g a) (x*y) := NearFn.mul H G H.bounded (Bounded.const _)
theorem sub (H : Near k f x) (G : Near k g y) : Near k (fun a=>f a-g a) (x-y) := NearFn.sub H G
theorem neg (H : Near k f x) : Near k (fun a=> -f a) (-x) := NearFn.neg H

theorem small (H : Near k f x) : Tendsto f k.along (𝓝 x) := NearFn.tendsto H tendsto_const_nhds

theorem inv (H : Near k f x) (hx : x≠0) : Near k (fun a=> (f a)⁻¹) x⁻¹ := by
  have he : ∀ᶠ a in k.along, |x| /2 < |f a| := H.small.abs.eventually (lt_mem_nhds (show |x|/2 < |x| from half_lt_self (abs_pos.mpr hx)))
  have hx' : 0 < |x|/2 := by exact half_pos (abs_pos.mpr hx)
  have hN : ∀ᶠ a in k.along, f a≠0:= he.mono fun _ h=> abs_pos.mp (lt_trans hx' h)
  apply NearFn.inv H _ (Bounded.const _) (hN.mono fun a h=> ⟨h,hx⟩)
  refine ⟨(|x|/2)⁻¹,inv_nonneg.mpr hx'.le,he.mono fun a (H: _ < |f a|)=>?_⟩
  rw [abs_inv]; simpa only [one_div] using (one_div_le_one_div_of_le hx' H.le)

theorem identify [k.along.NeBot] (H : Near k f x) (h : Near k f y) : x=y:= tendsto_nhds_unique H.small h.small

theorem congr (H : Near k f x) (he : g =ᶠ[k.along] f) : Near k g x := NearFn.congr H he (EventuallyEq.refl ..)
end Near
end YM.RG11.Rate
