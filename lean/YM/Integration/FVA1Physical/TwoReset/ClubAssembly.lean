import YM.Integration.FVA1Physical.TwoReset.PalettePages
import YM.Integration.FVA1Physical.TwoReset.ConstantRow

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open Primitives.TwoWave Primitives.TwoWave.RealSlice QuadraticLocal.Aperture AllOrder.Ker
open Laurent AllOrder.Ink QuadraticLocal.Echo QuadraticLocal.Poetry
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] [Fintype V] {c f C : Side}
  {J : Passport f V} {R : Census V} {p : ℕ} {a b : ℝ}
variable (M : ι→Row J R G α) (Q : Ratio c f)
    (B : Press M p) (L : Press.Receipt M B a b)
    (d : ℝ)
variable (h : c.val ∣ C.val) (t : α) (x : Stationary.Link G C) (i : ℕ)
local notation "Y" => Scene.letters M Q B L d
local notation "δ" => Pages c C
local notation "paint" => (fun i:ι=> (M i).paint t)
local notation "single" k:max => ScatterR.drawing M paint i k
local notation "impulse" => (fun j: Solo.Watching M=> Pages c C • ScatterR.drawing M (fun i=> (M i).paint t) i j.val)
local notation "all₁" => Scene.Texts M Q B
local notation "mixed" => (fun S:Club M=> periodic_cluster M Q B S h t x i)

omit [Fintype V] in
lemma reading_clear (j:Solo.Watching M)(u:Fin δ) :
    reading h Y t x i (Sum.inl j) u = single (j.val) := by
  let X : all₁ := Sum.inl j
  let F := TwoReset.copy h (Y X) u
  change Poly.send (M j.val).mode ((M j.val).paint t * ↑(F.markReceipt i x)) = _
  unfold ScatterR.drawing
  have he : Row.bearing F 1=Row.bearing (M j.val) 1:= by
    funext v
    unfold Row.bearing
    exact congr_arg (fun i:ℝ => (1:ℂ)*Complex.ofReal (v^(M j.val).lamp.stamp * i))
      (Solo.ghost (M j.val) j.prop (M j.val).center 1 F.center 1).symm
  have eq : Assembly.jet (Row.bearing F 1) (F.lamp.power+i) 1 =
      Assembly.jet (Row.bearing (M j.val) 1) ((M j.val).lamp.power+i) 1 := by rw [he]; rfl
  rw [Row.interest F 1 i j.prop x,Row.interest (M j.val) 1 i j.prop (0:_),one_mul,one_mul] at eq
  rw [eq]

variable (D : Layout G) (T : Finset Age) (w : V→ℕ)
variable {σ : ℝ} {o : ℕ}
variable (H : Air.Staff (Scene.letters M Q B L d) (fun j=> (Scene.letters M Q B L d j).paint t) w σ o)
include H

theorem repeated_formal_assembly : Summable impulse ∧ Summable mixed ∧
    peek h Y w D T t i x =
      (∑' j:Solo.Watching M,Pages c C • ScatterR.drawing M paint i j.val) +
        ∑' S:Club M,periodic_cluster M Q B S h t x i := by
  let f (z:all₁) := ∑ u:Fin δ, reading h Y t x i z u
  have hF : HasSum f (peek h Y w D T t i x) := total_peek h Y w D T t x i H
  have hx : f ∘ (Sum.inl: Solo.Watching M→ all₁) = impulse := by
    funext z
    change ∑ u:Fin δ,reading h Y t x i (Sum.inl z) u = _
    simp_rw [reading_clear M Q B L d h t x i z,sum_const,card_univ,Fintype.card_fin]
  have ha := hF.summable.comp_injective (Sum.inl_injective (α:=Solo.Watching M)
    (β:=Press.Runway M Q B))
  let g := f ∘ (Sum.inr: Press.Runway M Q B→ all₁)
  have hb : Summable g := hF.summable.comp_injective Sum.inr_injective
  have hz : HasSum mixed (∑' i:Press.Runway M Q B,g i):= hb.hasSum.sigma (fun j=>
    club_reading M Q B L d j h t x i w H)
  refine ⟨hx ▸ ha,hz.summable,?_⟩
  have huv := hF.unique (ha.hasSum.sum (f:=f) hb.hasSum)
  rw [huv,hx,hz.tsum_eq]

omit H
variable {C' F : Side}
omit [Fintype V] in
lemma clusters_scale (h' : C.val ∣ C'.val)(S : Club M) :
    periodic_cluster M Q B S (h.trans h') t (convey (coverWin h') x) i =
      Pages C C' • periodic_cluster M Q B S h t x i := by
  unfold periodic_cluster
  rw [← repeat_comp h h',production_convey,nsmul_eq_mul,Complex.ofReal_mul, Complex.ofReal_natCast,
    ← Nat.cast_smul_eq_nsmul ℂ (Pages C C'), mul_assoc,send_scale]

include h
lemma pages_mul (h' : C.val ∣ C'.val) : Pages c C'=Pages C C'*Pages c C:= by
  unfold Pages
  rw [← mul_pow]
  congr 1
  obtain ⟨v,hv⟩ := h
  obtain ⟨v',hv'⟩ := h'
  rw [hv', Nat.mul_div_cancel_left v' C.pos,hv,Nat.mul_div_cancel_left v c.pos,
    mul_assoc,Nat.mul_div_cancel_left (v*v') c.pos,mul_comm]

omit h
lemma pages_fine (θ : Ratio C F) (hθ : θ.count=Q.count) : Pages f F=Pages c C:= by
  unfold Pages
  rw [θ.exact_size,hθ,Q.exact_size,Nat.mul_div_mul_right _ _ Q.count.pos]

end YM.Integration.FVA1Physical.TwoReset
