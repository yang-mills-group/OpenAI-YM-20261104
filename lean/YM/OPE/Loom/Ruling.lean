import YM.OPE.Loom.Depot
/-!
# Exist comparison queries for this horizon at grid spacing ≤ v/T^4.
Spacing in local physical units; the cutoff still goes to UV frontier through the
chosen f; torus-lift and grid comparisons use that finer mesh. Stable, eventually
available on any collapsing length sequence.

Retain all hypotheses here. This supplies narrowed projected-capture estimates
from just the remaining (open) matching needs on `Origins`, not a theorem using
kcert even on its conditions.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies Next.Rank Next.UVStress PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Cells Extraction
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{T:Table C.book}{F:Spec.Final C f T}
variable {𝓛:Filter (ℕ×ℕ)} [𝓛.NeBot] {B:Frame.Scheme F} (L:Origins B 𝓛) {W r D}(A:Sharper C W r D)
variable {I J:Type}[Fintype J] [DecidableEq J]{t:ℕ} (d:ℕ)(s:J→ T.Tag) {φ:Filter I} {T' v : I→ℝ} {j:I→ℕ} {y a:ℝ}
variable (b:J)
include s L A b
-- queries return all sufficiently deep stops m; j fixed before specifying labels if v,T' given

omit s L A b in
def closeControl (C:Family G)(v T':ℝ) : ℕ:= Loom.observ 50 C (v/T'^4)
theorem arrange_grid (H : Services C f T) (hT:Tendsto T' φ atTop)(hx:Tendsto v φ (𝓝[>]0))(hv:RateIs φ T' v (-y))(ht:0<t) : let j i:= closeControl C (v i) (T' i)
    (∀ᶠ i in φ,C.S.a (j i)*(T' i)^4 ≤ v i)∧∀ᶠ m:ℕ in atTop, Desks F φ T' v B s b j a m d t :=by
    intro j; let k i:=arch 50 C (v i); let u i:=v i/(T' i)^4; let M i:=k i-1; have hu : Tendsto u φ (𝓝[>]0):= by
       apply tendsto_nhdsWithin_iff.mpr; have he:= ((hx.mono_right nhdsWithin_le_nhds).mul ((tendsto_inv_atTop_zero.comp hT).pow 4)); rw [zero_mul] at he
       refine ⟨he.congr (fun i=>?_ ),?_⟩; · unfold u; simp only [div_eq_mul_inv,Function.comp_apply,inv_pow]
       filter_upwards [hT.eventually_gt_atTop 0,hv.pos] with i hi ht; exact div_pos ht (pow_pos hi _)
    have hg:RateIs φ T' u (-y):= (hv.div ((flash hT).power 4)).swap (by simp)
    obtain ⟨hk,hP⟩:= arch_space 50 C hx hT hv A.tabs; obtain ⟨hj,hi⟩:= ordinary 50 C hu hT hg A.tabs
    have hU: Bi φ T' (C.S.a ∘ j) v:= by
       have hx:= Coins.by_le (Cheap.power (Cheap.id φ T') hT 4) (by
          filter_upwards [hT.eventually_ge_atTop 1] with i hi; exact (show (1:ℝ)≤ _ from one_le_pow₀ hi).trans (Real.le_norm_self _))
       refine hi.trans ?_; unfold u; simpa only [div_eq_mul_inv,mul_one] using Bi.mul (Bi.refl φ T' v) (Coins.inv hx)
    have hF:∀ᶠ i in φ, u i ≤ v i := ((hT.eventually_ge_atTop 1).and hv.pos).mono fun i hi=> div_le_self hi.2.le (one_le_pow₀ hi.1)
    constructor
    · filter_upwards [hg.pos,hT.eventually_gt_atTop 0] with i hi hT; refine (le_div_iff₀ (pow_pos hT _)).mp ?_; exact (gate_b (C:=C) 50 (j i)).trans ((broad_fits 50 C _).trans (fine_value 50 hi).le)
    filter_upwards [eventually_ge_atTop (C.ref d)] with m hm
    obtain ⟨k0,hk0⟩:= Stock.Tabs.mayOpen C.path.levels 1 A.tabs m
    have hS:=prec (m:=k) hk; have hZ:= (shift_back (C:=C) hT hk A.tabs).trans hP
    refine survey (t:=t) (j:=j) L A s b hS hj hT ?_ hx hU hZ ht (hm.trans hk0.1) hk0 H.schedule
    have hu₀:∀ᶠ i in φ, v i ≤ threshold C 50 0 := (hx.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds ((C.S.a_pos 0).trans_le (gate_b ..)))
    filter_upwards [hF,hk.grows.eventually_ge_atTop 1,hg.pos,hv.pos,hu₀,gates A t H.simpleGate J hx (k:=M) rfl (j:=j) m (by filter_upwards [hF,hg.pos] with i hi he using (fine_value 50 (C:=C) he).trans_le hi)] with i hf hk hi hw hh hp
    refine ⟨?_,hp.2⟩; change M i+1<_; rw [show M i + 1=k i from Nat.sub_add_cancel hk]; exact fine_all 50 hi (hf.trans ((arch_fails 50 hw (C:=C) hh).trans (broad_fits 50 C _)))
end YM.OPE.Loom
