import YM.OPE.Compatible.Pendulum.Luminescence
/-!
# Literal normalization of matching prices under stocks. Uniform in x (latitude chosen on leaves elsewhere)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U:Finset X}
   {G:Gauge}{C:Family G}{L:Extraction.Order}(A:Allot C)(hG:G.Simple){φ:Filter I}{s:I→X→ℝ}{T z c a:I→ℝ}
    {q:I→ℕ}(b d J :ℕ){η:ℝ}
set_option quotPrecheck false
local notation "K"=> C.S.a
local notation "f!"=> PhysicalNext.Repeat.Legato.Bandage.fly
include A hG
lemma exchanged_at (k:I→ℕ)(d:ℕ)(hk:Tendsto k φ atTop)(ht:Tendsto T φ atTop)(hv:Round φ T (fun i=> β C (k i)))(hz:Round φ T (fun i=>z i/a i))(hc:Round φ T c)(hh:∀ᶠ i in φ,0 < a i):
    ∃ r:I→ℝ, Round φ T (fun i=> r i/a i) ∧ ∀ᶠ i in φ,0<r i ∧ r i ≤ c i*badge_fee C (z i) (k i)∧ r i*(2*owed C (z i) d (k i)) ≤ c i^2*ballot C (k i) d∧ r i*‖alto C.path (k i) d‖*owed C (z i) d (k i)≤ f! C.path.levels d (k i):=by
   let u i:= owed C (z i) d (k i); let v i:= u i*z i/(K (k i)^d); let f i:= f! C.path.levels d (k i); let w i:=badge_fee C (z i) (k i); let t₀ i:= K (k i)^d; let t i:=‖alto C.path (k i) d‖; let a₁ i:=c i * w i; let a₂ i:= c i^2*ballot C (k i) d/(2*u i); let a₃ i:= f i / (t i * u i); let x i:=min (min (a₁ i) (a₂ i)) (a₃ i);
   have hν:∀ᶠ i in φ,0 < z i:= by
       filter_upwards [hz.pos,hh] with i he hp; exact (pos_of_mul_pos_left (by rwa [← div_eq_mul_inv] : 0 < z i*(a i)⁻¹) (inv_pos.mpr hp|>.le))
   have hx(i):t i=(K (k i)^d)⁻¹:=alto_norm .. -- maybe `(a^d)` inv? check
   have h':Round φ T v:= owed_cost A hG ht hk hv hν d
   have hf:Round φ T f := (hv.power (MergeProof.winter G d) ht).inv
   have h₁:Round φ T (fun i=>a₁ i / z i):=by
       have h0:= stepβ A hG ht hv.up
       refine (hc.div ((Round.const (a:=16) (by norm_num) ht).mul h0)).adjust ?_; filter_upwards [hν] with i hi; have hf:= β_pos C (k i+1)
       unfold a₁ w badge_fee; field_simp
   have h₂:Round φ T (fun i=> a₂ i / z i):=by
       apply (((hc.power 2 ht).mul hf).div ((Round.const (a:=4) (by norm_num) ht).mul h')).adjust; filter_upwards with i
       unfold a₂ v; rw [ballot]; unfold f; have hp:=pow_pos (C.S.a_pos (k i)) d; simp only [div_eq_mul_inv, mul_inv_rev,inv_inv]; ring
   have h₃:Round φ T (fun i=>a₃ i / z i):=by
       apply (hf.div h').adjust; filter_upwards with i; unfold a₃ v; rw [hx]; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
   have hU:Round φ T (fun i=>x i/z i):=by
       apply ((h₁.less h₂ ht).less h₃ ht).adjust; filter_upwards [hν] with i hi; unfold x; simp_rw [div_eq_mul_inv,min_mul_of_nonneg _ _ ((inv_pos.mpr hi).le)]
   refine ⟨x,(hU.mul hz).adjust ?_,?_⟩
   · filter_upwards [hν] with i hi; field_simp
   filter_upwards [hν,hU.pos,h'.pos] with i hi hp hζ
   have he:0<t i:=by rw [hx]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   have hu:0<u i:=by
       change 0 < u i * z i / _ at hζ; have ht:u i*z i>0:=pos_of_mul_pos_left (b:= (t₀ i)⁻¹) (by rwa [← div_eq_mul_inv]) (inv_pos.mpr (pow_pos (C.S.a_pos _) _)|>.le); exact pos_of_mul_pos_left ht hi.le
   have hg:x i ≤ min (a₁ i) (a₂ i):= min_le_left ..; rw [mul_assoc (x i) ‖_‖]
   exact ⟨pos_of_mul_pos_left (b:=(z i)⁻¹) (by rwa [← div_eq_mul_inv]) (inv_pos.mpr hi|>.le),hg.trans (min_le_left ..), le_div_iff₀ (mul_pos zero_lt_two hu)|>.mp (hg.trans (min_le_right ..)), (le_div_iff₀ (mul_pos he hu)).mp (min_le_right ..)⟩
end YM.OPE.Arboreal.Pixel
