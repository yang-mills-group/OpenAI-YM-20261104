import YM.Integration.WilsonIndependentFreshCopySeam
import YM.RegulatorIR.Halo.Choir

/-! The finite occupied Taylor coefficients on the original captured history
tend to the actual infinite-lattice coefficients along enlarged copies. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentFreshCopyLimit
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Halo.Sight
open RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet RegulatorIR.Budget.Deck RegulatorIR.Budget.Tuple
open RegulatorIR.Uniform RegulatorIR.Spatial RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ward
open RegulatorIR.Step RegulatorIR.Halo.Aug RegulatorIR.Motion
open WilsonIndependentFreshReplica WilsonIndependentFreshCopyWage
open Set Filter PowerSeries
open scoped Topology ENNReal BigOperators PowerSeries ContDiff
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}

variable (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p k m s a : ℕ} (B : S.Primitive L p k)
  (Z : (E.part S T B).Report m) (w : W)
local notation "Zc" => report H T quiet large E B Z w

variable (bank : S.Supplies T L p k) (C : Amenities S L p k) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))

variable (j : ℕ) (hj : j ≤ E.spans w)
local notation "d" => E.age w+j
local notation "hv" => absAge E w hj
local notation "x0" => (Page.mk w j hj : Page E.spans)
local notation "xs" => sheetAt E w j hj
local notation "xb" => Aug.sheet w (E.age w+j) (absAge E w hj)
local notation "Ep" => eternal H w
variable (X : (z : Side) → ℝ → Horizon G (big w n (Aug.sheet w (E.age w+j) (absAge E w hj) z))) (u : Foot G → ℝ⟦X⟧)
include stamp bank C quiet large
lemma cusp {r i:ℕ} (z:Side)(hi:i ≤ p): quota ((Zc).main (xs z) i r) 1≠⊤:=by
 have ht:= rooted (a:=0) H T quiet large E B Z w bank C film stamp j hj (by omega) _ hi r
 exact ne_top_of_le_ne_top (ht.cost z (by change (1:ℝ≥0∞)≠⊤; finiteness)) (quota_mono _ fun i=>Premium.width_unit ..)
lemma cusp_b (r i:ℕ)(hi:i ≤ p): quota (Z.main x0 i r) 1 ≠⊤:=by
 have ht:= rooted (a:=0) H T quiet large E B Z w bank C film stamp j hj (by omega) _ hi r
 have hh:= ht.cost 1 (by change (1:ℝ≥0∞)≠⊤; finiteness)
 rw [relocate (a := 0) H T quiet large E B Z w j hj 1 i r] at hh; exact ne_top_of_le_ne_top hh (quota_mono _ fun i=>Premium.width_unit ..)
variable (R : Aria H w (E.age w+j) (absAge E w hj) X u (p:=p))
include R
omit R in
lemma inked (z:Side){e r:ℕ}(hi:e ≤ p) k: rhyme (vow (peel (X z))) (((Ep).maps (xb z)).scroll ((Zc).main (xs z) e r)) k= rhyme (cue H w (E.age w+j) (absAge E w hj) z (X z)) (Z.main x0 e r) k:=by
 rw [chord_port _ _ (cusp H T quiet large E B Z w bank C film stamp j hj z hi)]
 exact rhyme_echo ..
lemma melodic (e:ℕ)(he:e≤p): let T(z:Side):Orders (Book G (big w n (xb z))):= fun i r=> ((Ep).maps (xb z)).scroll ((Zc).main (xs z) i r); Tendsto (fun z=> coeff e (reel (T z) m (X z))) atTop (𝓝 (rhymeR u (Z.main x0) m e)) :=by
 intro T'; simp_rw [rhyme_tube,rhymeR]
 have hX : Full (fun z=>cue H w (E.age w+j) (absAge E w hj) z (X z)) p:=by
    intro i hi; obtain ⟨c,he,F⟩:= R.ful i hi; refine ⟨c,he,fun x y=>?_⟩; change ‖coeff i (chord _ _ _)‖ₑ≤ _; rw [chord_k];exact F x _
 apply tendsto_finsetSum; intro p hp'; have hs:= Finset.mem_antidiagonal.mp hp'
 apply tendsto_finsetSum; intro i _
 simp_rw [T',inked H T quiet large E B Z w bank C film stamp j hj X _ (show p.1 ≤ _ by omega)]; exact R.learnK.price (by omega) _ (cusp_b H T quiet large E B Z w bank C film stamp j hj _ _ (by omega)) hX
variable (hk : 14 ≤ k)
include hk
lemma chorus (e:ℕ)(hi:e≤p): Tendsto (fun z=> coeff e (reel ((Zc).point (xs z)) m (X z))) atTop (𝓝 (rhymeR u (Z.main x0) m e)):=by
 let T'(z:Side):Orders (Book G (big w n (xb z))):=fun i r=> ((Ep).maps (xb z)).scroll ((Zc).main (xs z) i r)
 let A(z:Side) : Orders (Book G (big w n (xb z))) := (Zc).point (xs z);let a(z:Side):=coeff e (reel (A z) m (X z)); let t(z:Side):=coeff e (reel (T' z) m (X z))
 let f(z:Side)(e:ℕ)(i:ℕ):=(Zc).deviation (xs z) e i
 have hp' : Carry Aug.light Aug.debt fun z=> ‖a z-t z‖ₑ :=by
    have hs(z:Side):a z - t z= rhymeR (vow (peel (X z))) (f z) m e:=by
       unfold a t;rw [← map_sub,← rhyme_tube, show f z=A z-T' z from rfl]; unfold reel; rw [reel_split,map_sub,map_sub,map_sub]
    simp_rw [hs]; apply songs_many (Y:=fun z=> Book G (big w n (xb z))) _ (fun i h=>R.ful i (h.trans hi))
    intro i lower l; exact Carry.mono (WilsonIndependentFreshCopySeam.winding H T quiet large E B Z w bank C film stamp j hj hk i (lower.trans hi) l) (fun w=>quota_mono _ fun i=>Premium.width_unit ..)
 change Tendsto a atTop _; rw [show a=(fun z=>a z-t z) + t from by ext1 x; exact (sub_add_cancel ..).symm]; convert (debt_vanish hp').add (melodic H T quiet large E B Z w bank C film stamp j hj X u R e hi) using 1 <;> first|rfl | simp


end YM.Integration.WilsonIndependentFreshCopyLimit
