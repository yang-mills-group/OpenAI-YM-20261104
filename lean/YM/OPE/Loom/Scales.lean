import YM.OPE.Loom.Native
/-! # Brackets on an arbitrary scale path for positive finite horizon analysis.

Counter propagation from arch to origin will pay the same β costs as leaves at the
fine grid. Doesn't require `a` match to an arbitrary cutoff (held fixed first).
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
variable {G:Gauge} {C:Family G} {I : Type*} {φ : Filter I} {T a c d : I→ℝ} {m k : I→ℕ} {b v : ℝ}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "P" => C.path.levels.budget
set_option quotPrecheck false
lemma straddles (C:Family G)(h:Tendsto m φ atTop)(c d:ℕ→ℝ) (hT:Tendsto T φ atTop) (hc:RateIs atTop C.S.scale c (-1)) (hd:RateIs atTop C.S.scale d (-1)) (ha:RateIs φ T a (-b)) (he:∀ᶠ i in φ,c (m i) ≤ a i ∧ a i ≤ d (m i)) : Height C.S φ T m b:=by
   have h₁:= hc.rate.comp h; have h₂:=hd.rate.comp h; let y i:= C.S.scale (m i); let r i:= -(Real.log (a i)); have hz:= ha.rate; have hr : Tendsto (fun i=>r i/T i) φ (𝓝 b):= by simpa only [←neg_div,neg_neg] using hz.neg
   have hp (a:ℕ→ℝ)(H:Tendsto (fun i=>Real.log (a (m i))/y i) φ (𝓝 (-1))) : Tendsto (fun i=> r i/T i/(-(Real.log (a (m i)))/y i)) φ (𝓝 b):=by
       have ht : Tendsto (fun i=>-(Real.log (a (m i)))/y i) φ (𝓝 1) := by simpa only [← neg_div, neg_neg] using H.neg
       simpa only [div_one] using! hr.div ht one_ne_zero
   let f i:=-(Real.log (c (m i))); let g i:=-(Real.log (d (m i))); have hf : ∀ᶠ i in φ,0<f i/y i :=by have hx:= h₁.eventually (gt_mem_nhds (show (-1:ℝ)<0 by norm_num)); filter_upwards [hx] with i hi using (neg_div (Real.log _) _).trans_gt (neg_pos.mpr hi) -- direction
   have hg : ∀ᶠ i in φ,0<g i/y i:=by filter_upwards [h₂.eventually (gt_mem_nhds (show (-1:ℝ)<0 by norm_num))] with i hi using (neg_div (Real.log _) _).trans_gt (neg_pos.mpr hi)
   have hz : ∀ᶠ i in φ, r i/T i/(f i/y i) ≤ y i/T i ∧ y i/T i ≤ r i/T i/(g i/y i):=by
      filter_upwards [hf,hg,he,hT.eventually_gt_atTop 0,((C.S.divergent.comp h).eventually_gt_atTop 0),h.eventually hc.pos,ha.pos] with i hu hv hi hT hy hx ha
      have hy:0<y i:=hy; rw [div_le_iff₀ hu,le_div_iff₀ hv]
      have hh (u:ℝ) : y i/T i*(u/y i)=u/T i:= by field_simp
      rw [hh,hh]; exact ⟨div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hx hi.1)) hT.le,div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log ha hi.2)) hT.le⟩
   exact ⟨h,tendsto_of_tendsto_of_tendsto_of_le_of_le' (hp c h₁) (hp d h₂) (hz.mono fun _ h=>h.1) (hz.mono fun _ h=>h.2)⟩
variable (K:ℕ)
lemma arch_space (C:Family G)(h:Tendsto a φ (𝓝[>]0))(hT:Tendsto T φ atTop)(ha:RateIs φ T a (-b))(H:Stock.Tabs C.path.levels) : let k i:= arch K C (a i)
          Height C.S φ T k b ∧ Bi φ T (fun i=>C.S.a (k i)) a :=by
   intro k; let m i:= k i+1; have hu:Tendsto k φ atTop:= arch_growth K C h
   have hb : ∀ᶠ i in φ,a i ≤ threshold C K (k i):= ((h.eventually (Ioc_mem_nhdsGT ((C.S.a_pos 0).trans_le (gate_b K 0))))).mono fun i hi=> arch_fails K hi.1 hi.2
   have hv : ∀ᶠ i in φ,C.S.a (m i) ≤ a i := ha.pos.mono fun i hi=> (gate_b K (m i)).trans (before K hi (show k i < m i from Nat.lt_succ_self _)).le
   have ht:= straddles C hu (fun i=>C.S.a (i+1)) (threshold C K) hT ((first_price.step C.path.levels.fits.mesh).mesh) (threshold_rate (C:=C) C.S.divergent first_price K) ha (hv.and hb)
   refine ⟨ht,(shift_mesh hT ht H).symm.trans ?_⟩
   have he:= Bill.made (T:=T) (F:=a) (a:=fun i=>threshold C K (k i)) ((hb.and ha.pos).mono fun i ⟨hh,h₀⟩=> (Real.norm_of_nonneg h₀.le).trans_le (hh.trans (Real.le_norm_self _)))
   refine ⟨Bill.made ((hv.and ha.pos).mono fun i ⟨hi,h⟩=> ?_),he.trans ((threshold_cost hT ht K).up.trans (shift_mesh hT ht H).down)⟩
   exact (Real.norm_of_nonneg ((C.S.a_pos _)|>.le)).trans_le (hi.trans (Real.le_norm_self _))
end YM.OPE.Loom
