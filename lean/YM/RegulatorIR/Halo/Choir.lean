import YM.RegulatorIR.Halo.Lamps

/-!
# Ward on marked pullbacks

If transformed along tested native curves approximated by the regulators,
locality from positive-order soft transmission gives cover and perSrc Ward.
Finite stack and all insertion coefficients at each stated pledge. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{f:Side}{P:ℝ}{k p m i a r s:ℕ} {W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G}
variable (H:Reel S) (T:S.Accounts)(Z:T.Report m)(w:W){L:Meter W}
variable (B: S.Supplies T L p k)(C: Aug.Amenities S L p k) (h':14≤k)(hp:H.Follows T)
variable (hc:Common H){U:W→Portrait G}(hU:∀ x,BasisT m s (U x) (Z.main (Page.opening M x)))
variable (j:ℕ)(h:j ≤ M w)
local notation "E0" => eternal H w
local notation "P0" => tele H T w
local notation "B0" => gazer H T Z w hp
local notation "C0" => Aug.sheet w j h
local notation "x₀" => (Page.mk w j h)

-- uses `Full` orientation script estimates. 

def cue (z:Side)(x:ℝ→ Horizon G (big w n (Aug.sheet w j h z))): Foot G→ℝ⟦X⟧:=chord (Sight.radar H w (Aug.sheet w j h z)) (vow (peel x)) ∘ shiftE (S:=S) w (Aug.sheet w j h z)
variable (X: (z:Side)→ℝ→ Horizon G (big w n (Aug.sheet w j h z))) (u:Foot G→ℝ⟦X⟧)
def coloring (X: (z:Side)→ℝ→Horizon G (big w n (Aug.sheet w j h z))): (z:Side)→ Book G (big w n (Aug.sheet w j h z))→ℝ⟦X⟧:=fun z=>vow (peel (X z))
structure Aria : Prop where
 rays : ∀ z,ContDiffAt ℝ ∞ (X z) 0
 learnK : Learn u (fun z=>cue H w j h z (X z)) atTop p
 ful : Full (coloring w j h X) p

include B C hp hc hU
lemma cusp {r i:ℕ} (z:Side)(hi:i ≤ p): quota ((B0).main (C0 z) i r) 1≠⊤:=by
 have ht:= Aug.core_mark H w T hp Z B C hc hU _ h (a:=0) (by omega) _ hi r
 exact ne_top_of_le_ne_top (ht.cost z (by change (1:ℝ≥0∞)≠⊤; finiteness)) (quota_mono _ fun i=>Premium.width_unit ..)
lemma cusp_b (r i:ℕ)(hi:i ≤ p): quota (Z.main x₀ i r) 1 ≠⊤:=by
 have ht:= Aug.core_mark H w T hp Z B C hc hU _ h (a:=0) (by omega) _ hi r
 have hh:= ht.cost 1 (by change (1:ℝ≥0∞)≠⊤; finiteness)
 rw [show markQ _ (gazer H T Z w hp|>.main (C0 1) i r)= _ from Aug.relay_cost H w T hp Z _ h 1 i r (a:=0)] at hh; exact ne_top_of_le_ne_top hh (quota_mono _ fun i=>Premium.width_unit ..)
variable (R : Aria H w j h X u (p:=p))
include R
omit R in
lemma inked (z:Side){e r:ℕ}(hi:e ≤ p) k: rhyme (vow (peel (X z))) (((E0).maps (C0 z)).scroll ((B0).main (C0 z) e r)) k= rhyme (cue H w j h z (X z)) (Z.main x₀ e r) k:=by
 rw [chord_port _ _ (cusp H T Z w B C hp hc hU j h z hi)]
 exact rhyme_echo ..
lemma melodic (e:ℕ)(he:e≤p): let T(z:Side):Orders (Book G (big w n (C0 z))):= fun i r=> ((E0).maps (C0 z)).scroll ((B0).main (C0 z) i r); Tendsto (fun z=> coeff e (reel (T z) m (X z))) atTop (𝓝 (rhymeR u (Z.main x₀) m e)) :=by
 intro T'; simp_rw [rhyme_tube,rhymeR]
 have hX : Full (fun z=>cue H w j h z (X z)) p:=by
    intro i hi; obtain ⟨c,he,F⟩:= R.ful i hi; refine ⟨c,he,fun x y=>?_⟩; change ‖coeff i (chord _ _ _)‖ₑ≤ _; rw [chord_k];exact F x _
 apply tendsto_finsetSum; intro p hp'; have hs:= Finset.mem_antidiagonal.mp hp'
 apply tendsto_finsetSum; intro i _
 simp_rw [T',inked H T Z w B C hp hc hU j h X _ (show p.1 ≤ _ by omega)]; exact R.learnK.price (by omega) _ (cusp_b H T Z w B C hp hc hU j h _ _ (by omega)) hX
include h'
lemma chorus (e:ℕ)(hi:e≤p): Tendsto (fun z=> coeff e (reel ((B0).point (C0 z)) m (X z))) atTop (𝓝 (rhymeR u (Z.main x₀) m e)):=by
 let T'(z:Side):Orders (Book G (big w n (C0 z))):=fun i r=> ((E0).maps (C0 z)).scroll ((B0).main (C0 z) i r)
 let A(z:Side):= (B0).point (C0 z);let a(z:Side):=coeff e (reel (A z) m (X z)); let t(z:Side):=coeff e (reel (T' z) m (X z))
 let f(z:Side)(e:ℕ)(i:ℕ):=(B0).deviation (C0 z) e i
 have hp' : Carry Aug.light Aug.debt fun z=> ‖a z-t z‖ₑ :=by
    have hs(z:Side):a z - t z= rhymeR (vow (peel (X z))) (f z) m e:=by
       unfold a t;rw [← map_sub,← rhyme_tube, show f z=A z-T' z from rfl]; unfold reel; rw [reel_split,map_sub,map_sub,map_sub]
    simp_rw [hs]; apply songs_many (Y:=fun z=> Book G (big w n (C0 z))) _ (fun i h=>R.ful i (h.trans hi))
    intro i hj l; exact Carry.mono (Aug.march_bill H w T hp Z B C hc hU j h h' i (hj.trans hi) l) (fun w=>quota_mono _ fun i=>Premium.width_unit ..)
 change Tendsto a atTop _; rw [show a=(fun z=>a z-t z) + t from by ext1 x; exact (sub_add_cancel ..).symm]; convert (debt_vanish hp').add (melodic H T Z w B C hp hc hU j h X u R e hi) using 1 <;> first|rfl | simp

variable {X u}
theorem harmony {v:Foot G→ℝ⟦X⟧}{Y: (z:Side)→ℝ→ Horizon G (big w n (Aug.sheet w j h z))} (F:Aria H w j h Y v (p:=p))(hr:∀ z,reel_prop (X z) (Y z)){e:ℕ}(he:e ≤ p):rhymeR u (Z.main x₀) m e=rhymeR v (Z.main x₀) m e := by
 apply tendsto_nhds_unique (chorus H T Z w B C h' hp hc hU j h X u R e he)
 have hp' := chorus H T Z w B C h' hp hc hU j h Y v F e he
 convert hp' using 1; ext1 z; obtain ⟨K⟩:= glowing H T Z hp U hU w hc (C0 z); exact congr_arg (fun w:PowerSeries ℝ=> coeff e w) (Ward.RangeR.stamps (K:= (grove H w hc).stance _) K (R.rays z) (F.rays z) (hr z))
end YM.RegulatorIR.Halo
