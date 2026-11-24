import YM.Contact.Arose
import YM.MergeProof.North.Welch
import YM.Progress.CLASSICAL_KIN_RECURSION.Weir
import YM.Push.LOOP_COEFFICIENT.Block.Explain
import YM.Push.LOOP_COEFFICIENT.Fine.Budgets
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d w:ℕ)(h:ℤ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop) -- notation binder
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable {b a:ℝ}(hb:0<b)(ha:0<a)(hp:(D:ℤ)+h=d+w)
local notation "F"=> fun i=> fuga C.path.levels (i+1)
local notation "A"=> fun (i:ℕ)=> twoStakes C (j i) i d w h b a
local notation "Z'"=> fun (i:ℕ)=> holder C.path.levels (j i) i δ η (δ (i+1)) ((A) i)
local notation "N"=>Note C.S
local notation "M"=> (((d:ℝ)+(w:ℝ)+8)*(1-t))
open Accent
set_option quotPrecheck false
local notation "K'"=> (fun i=> ((J (i+1)).supportExponent+1/2)*countStem C.path.levels i)
structure Tally (T:Levels G):Prop where
  costs (i:ℕ) : ((T.budget (i+1)).supportExponent+(1:ℝ)/2)*(↑(countStem T i):ℝ)≤(Real.sqrt (T.clock.hatBeta (i+1)))
variable (hL:Tally (C.path.levels))
include hj hT hV hG hL
omit hj hT hV in
lemma invoice : N (fun i=>Real.exp (K' i)) 0:= by
    have hp:= banket C hG|>.pitch; unfold bling at hp; simp only [Real.log_exp] at hp
    refine ⟨fun i=>Real.exp_pos _, ?_⟩
    simp_rw [Real.log_exp]; apply squeeze_zero' _ _ hp
    · exact Eventually.of_forall (fun i=>div_nonneg (mul_nonneg (add_nonneg ((J (i+1)).exponent_pos.le) (by norm_num)) (Nat.cast_nonneg _)) (Shoot.scale_nn _ _))
    exact Eventually.of_forall (fun i=>div_le_div_of_nonneg_right (hL.costs i) (Shoot.scale_nn _ _))
omit hV in
lemma flute {w:ℕ→Bool→ℝ}(v:Bool)(hw:N (fun i=>w i v) x): N (fun i=> pickEl C.path.levels (j i) i δ η (δ (i+1)) (w i) v) (x+4*(1-t)):=by
   have hh:C.S.Gentle:=C.path.levels.fits.mesh; obtain ⟨hs,he⟩:= mintN C hG
   have hF:=Note.note_a C.S; have hx:= ((hs.relay j hj hT).mills ((he.relay j hj hT).mills hw)).splits (Note.notes C.S 16 (by norm_num)); have hb := ((hF.relay j hj hT).splits ((hF.scales hh).scales hh)).powerN 4 -- ratio
   exact (((hs.scales hh|>.mills ((hs.scales hh).mills (hx.mills hb))).splits (invoice C hG hL)).swapP (by push_cast; ring))
include D hp ha hb
lemma sea_charge : Note C.S Z' (-D + M) :=by
   have hg:= plumN C d hG a ha|>.relay j hj hT; have he:= ((plumN C w hG b hb).relay j hj hT).splits (((fuchsia C hG hV).scales C.path.levels.fits.mesh).powr (h:ℝ)); unfold holder
   apply ((flute _ hG _ hT hj hL (w:=A) false (by exact hg)).mills (flute _ hG _ hT hj hL (w:=A) true (by simpa only [Real.rpow_intCast] using! he))).swapP
   have hi:(d:ℝ)+(w:ℝ)-(h:ℝ)=D:=by exact sub_eq_of_eq_add (by exact_mod_cast hp.symm)
   push_cast; rw [←hi]; ring
end YM.MergeProof.Ribbons
