import YM.Frontier6.Pair.Mutation
import YM.Frontier6.Pair.Span
import YM.MergeProof.North.Burrough

/-!
# Capture price, including between-level shells.

Constants path dependent. `longHalo` is big enough to enclose from the
inner level all the pairs with separation just below the previous (coarser)
level's sparse annulus. Linear cover-number matters. We charge s^{o(1)} in
exp(log scale) units (i.e. arbitrary power loss, **not** a bound by a power
of the log).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem leading_support (A:Levels G)(i:ℕ) :
    (A.budget (i+1)).supportExponent + 1/2 ≤ (A.S.block i).val := by
  let Z := A.params (i+1)
  let K : ℝ := 1+Z.paths+Z.width⁻¹+Z.columns+Z.clip.relaxation+Z.supportExponent
  let L : ℝ := (A.S.block i).val
  let J : ℝ := A.clock.J (i+1)
  have ht : Real.log K / Real.log L ≤ (J^2)⁻¹ := A.fits.logCost i
  have h₁ : 1 < L := by unfold L; exact_mod_cast (show 1 < (A.S.block i).val from lt_of_lt_of_le (by norm_num) (A.S.block_large i))
  have h : 1 ≤ J := by unfold J; exact_mod_cast (le_trans (by norm_num) (A.clock.adm (i+1)) : 1 ≤ A.clock.J (i+1))
  have hcost : Real.log K ≤ Real.log L := by
    apply (div_le_one (Real.log_pos h₁)).mp; exact ht.trans (inv_le_one_of_one_le₀ (one_le_pow₀ h))
  have hz : Z.supportExponent + 1/2 ≤ K := by
    unfold K; linarith [Z.paths_pos, Z.columns_ge, inv_pos.mpr Z.width_pos, Z.clip.radius_pos]
  exact hz.trans ((Real.log_le_log_iff (lt_of_lt_of_le (by linarith [Z.price_pos]) hz) (zero_lt_one.trans h₁)).mp hcost)

private theorem fiat_one (A : Levels G) (i : ℕ) : 1 ≤ Vac.fiat G (A.params i) (A.clock.hatBeta i) := by
    let b:= A
    unfold Vac.fiat
    have he := (A.params i).paths_pos
    have ha := (A.params i).clip.quadratic_pos
    have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((A.params i).clip.direct + (A.params i).paths^2) +
      4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (A.clock.hatBeta i)/2) := by
      have hu := Real.log_pos (A.fits.delayed i)
      positivity
    linarith only [hp,he]

/-- The whole fusion cover charge at the chosen block. -/
def longHalo (A:Levels G)(i:ℕ): ℝ :=
    ((A.budget (i+1)).supportExponent+1/2)*↑(4*fusionSpan A i+1)

private theorem path_compare (A:Levels G)(i:ℕ) :
    longHalo A i ≤ 2053*((A.S.block i).val*((A.clock.coverSize i:ℝ)^2))^4*
      Vac.fiat G (A.params (i+1)) (A.clock.hatBeta (i+1)) := by
   let L : ℝ := (A.S.block i).val; let B : ℝ := (A.budget i).B; let X := L * B^2
   have hL : 1 ≤ L := by unfold L; exact_mod_cast (show 1 ≤ (A.S.block i).val from (A.S.block i).property)
   have hB : 1 ≤ B := by unfold B; exact_mod_cast (show 1 ≤ (A.budget i).B from (A.budget i).B_pos)
   have hv : L ≤ X := le_mul_of_one_le_right (zero_le_one.trans hL) (one_le_pow₀ hB)
   have hx : 1 ≤ X := hL.trans hv
   have ht : (↑(4*fusionSpan A i+1) : ℝ) ≤ 2053*X := by
      suffices he : (↑(4*fusionSpan A i+1):ℝ) = 5 + 2048*X by rw [he]; linarith
      unfold fusionSpan X L B; push_cast; ring
   let f := Vac.fiat G (A.params (i+1)) (A.clock.hatBeta (i+1))
   apply le_trans (mul_le_mul ((leading_support A i).trans hv) ht (Nat.cast_nonneg _) (zero_le_one.trans hx))
   change X*(2053*X) ≤ 2053*X^4*f
   exact le_trans (by nlinarith only [pow_le_pow_right₀ hx (show 2≤4 by decide)] : X* (2053*X) ≤ 2053*X^4) (le_mul_of_one_le_right (by positivity) (fiat_one A _))

lemma halo_billed (A : Levels G)(hB:Stock.Tabs A) : Note A.S (fun i=>Real.exp (longHalo A i)) 0:=by
    refine ⟨fun i=>Real.exp_pos _,?_⟩
    simp_rw [Real.log_exp]
    have hv:Tendsto (fun i=>longHalo A i/A.S.scale (i+1)) atTop (𝓝 0):=by
       refine (Metric.tendsto_nhds).mpr fun ε hε=>?_
       filter_upwards [hB.cheap (ε/4106) (by positivity),(A.S.divergent.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop 0] with i hi hx
       have hx : 0 < A.S.scale (i+1):=hx
       rw [dist_zero_right,Real.norm_of_nonneg (?_)]
       · apply (div_lt_iff₀ hx).mpr
         linarith only [path_compare A i,hi, mul_pos hε hx]
       exact div_nonneg (by unfold longHalo; positivity [(A.budget (i+1)).exponent_pos]) hx.le
    have he:= Note.bell_exp A.S 1|>.scales A.fits.mesh|>.pitch; simp_rw [Real.log_exp,one_mul] at he
    refine ((show Tendsto (fun i=>longHalo A i/A.S.scale (i+1) * (A.S.scale (i+1)/A.S.scale i)) atTop (𝓝 0) from by simpa using! hv.mul he)).congr' (?_)
    filter_upwards [(A.S.divergent.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop 0] with i hi
    have hx:0 < A.S.scale (i+1):=hi; field_simp

variable (C:Family G)(hG:G.Simple) {d D D':ℕ}
variable {j:ℕ→ℕ}{t z:ℝ}(hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t))(hj:Tendsto j atTop atTop)
variable (hB:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "N"=> Note C.S

include hG hB hT hj
lemma offsetPicket {w:ℕ→Bool→ℝ}(v:Bool)(hw:N (fun i=>w i v) z): N
   (fun i=> longPicket C.path.levels (j i) (i+1) (fusionSpan C.path.levels i) δ η (δ (i+1)) (w i) v) (z+4*(1-t)):=by
   have hh:C.S.Gentle:=C.path.levels.fits.mesh; obtain ⟨hs,he⟩:= mintN C hG
   have hF:=Note.note_a C.S; have hx:= ((hs.relay j hj hT).mills ((he.relay j hj hT).mills hw)).splits (Note.notes C.S 16 (by norm_num))
   have hb := ((hF.relay j hj hT).splits ((hF.scales hh).scales hh)).powerN 4
   exact (((hs.scales hh|>.mills ((hs.scales hh).mills (hx.mills hb))).splits (halo_billed C.path.levels hB)).swapP (by push_cast; ring))

omit hG hT hj hB
def partnerRates (C:Family G) (j d d':ℕ)(b b':ℝ) (v:Bool):ℝ:=if v then Accent.plumR C d' b' j else Accent.plumR C d b j

def pairLaunch (C:Family G)(j i d d':ℕ)(b b':ℝ):ℝ:= longVent C.path.levels j (i+1) (fusionSpan C.path.levels i) (renal C.path.levels) (near C.path.levels) (renal C.path.levels (i+1)) (partnerRates C j d d' b b')
-- raw pair quota envelope at capture
local notation "X"=>bling C.path.levels
def pairQuota (C:Family G)(j i d d' D:ℕ)(b b':ℝ):ℝ:=
  4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^D*(bling C.path.levels i*(4*(1/(pairLaunch C j i d d' b b'))))))
def exteriorReserve (C:Family G)(i:ℕ)(d d' D:ℕ) (y:ℝ):ℝ:=
  Real.exp (((D:ℝ)-(d:ℝ)-(d':ℝ)+y)*C.S.scale i)

variable {b a:ℝ}(hb:0<b)(ha:0<a)
local notation "Z'"=> fun (i:ℕ)=> pairLaunch C (j i) i d D' b a
local notation "M"=> (((d:ℝ)+(D':ℝ))*t+8*(t-1))
include hG hT hj hB hb ha
lemma offsetVent : N (Z') (- M):=by
   have hg:= plumN C d hG b hb|>.relay j hj hT; have he:= (plumN C D' hG a ha|>.relay j hj hT); unfold pairLaunch longVent
   refine ((offsetPicket _ hG hT hj hB (w:=fun i=>partnerRates C (j i) d D' b a) false (z:=-(d:ℝ)*t) ?_).mills (offsetPicket _ hG hT hj hB (w:=fun i=>partnerRates C (j i) d D' b a) true (z:=-(D':ℝ)*t) ?_)).swapP (by ring)
   · exact hg
   exact he
local notation "e"=> fun i=> pairQuota C (j i) i d D' D b a
lemma quotaPitch : N e (-(D:ℝ)+M):=by
   let S:= C.S; have hx:= offsetVent (d:=d) (D':=D') C hG hT hj hB hb ha; have hy:= Note.note_a S; have hf:= banket C hG
   let v i:= 1+(C.path.levels.params i).columns
   have hz: N v 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have haD:= (Note.note_a S).scales C.path.levels.fits.mesh |>.powerN D
   have hE: N e (-(D:ℝ)+(M)):= by
       have h₀:=Note.notes S 4 (by norm_num); exact (((h₀.mills hz).mills ((Note.notes S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills ((Note.notes S 1 one_pos).splits hx)))))).swapP (by ring))
   exact hE

open Accent Source Extra.Histories
variable {u ψ:ℕ→ℝ}{W:Worth}{r:ℕ→ℕ}{A:∀ n p m:ℕ,m<n→GaugeDoor (C.path.rep n p (m+1)) (C.path.rep n p m)}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r A) (y:ℝ)
local notation "c"=>fun i=> exteriorReserve C i d D' D y
local notation "Q"=> C.S.scale
include hW y
lemma offset_price (k:ℕ)(hK:C.ref D ≤ k)(he: y+M < (1/8)+(d:ℝ)+(D':ℝ)) : ∀ᶠ i in atTop, (0<(Z') i ∧ march (fun _:Unit=>(c) i) η k i () ≤ δ i * (((Z') i)/(16*X i)))∧ 32*(1+(C.path.levels.params i).columns)* (c) i * ‖alto C.path k D‖*((e) i/gainChart C.path i k) ≤ fly C.path.levels D k/2:=by
   let S:= C.S; have ht:N (c) ((D:ℝ)-(d:ℝ)-(D':ℝ)+y):= Note.bell_exp S _; have hx:= offsetVent (d:=d) (D':=D') C hG hT hj hB hb ha; have hy:= Note.note_a S; have hf:= banket C hG
   let q:= fly C.path.levels D k; have hq:0<q:= hW.grows _ _ hK
   have hr:= (Note.notes S 16 (by norm_num)).mills hf; have hI:= (mintN C hG).1.mills (hx.splits hr)
   let v i:= 1+(C.path.levels.params i).columns
   let w:= ‖alto C.path k D‖; have hw:0 < w:=by unfold w; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   have hz: N v 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hc:= ((Note.notes C.S 32 (by norm_num)).mills hz).mills ht|>.mills (Note.notes _ w hw)
   have hE: N e (-(D:ℝ)+(M)):= quotaPitch (D:=D) C hG hT hj hB hb ha
   have hF:N (fun i=>gainChart C.path i k) (1/8):=by
       let r:ℝ:=Real.exp ((1/8:ℝ)*Q k)
       have hv:= (Note.bell_exp S (1/8)).splits (Note.notes S r (Real.exp_pos _))
       unfold gainChart; simp_rw [mul_sub,Real.exp_sub]; exact hv.swapP (sub_zero _)
   have hH:= (hc.mills (hE.splits hF)).outweigh (Note.notes C.S (q/2) (half_pos hq)) (by linarith)
   let u i:= ((c) i)* (S.a i/S.a k)^(D+1)*(1/q)
   have hJ:= (ht.mills ((hy.splits (Note.notes S _ (S.a_pos k))).powerN (D+1))).mills (Note.notes S (1/q) (by positivity)); have hh:=hJ.outweigh hI (by push_cast; linarith)
   filter_upwards [eventually_ge_atTop k,hH,hh] with i hi hk hh
   have hU := seeing C D hW (ht.pos i) i k hK hi
   refine ⟨⟨hx.pos _,hU.trans (le_trans ?_ hh)⟩,hk⟩
   apply mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (fly_le C i D) hq.le) (mul_nonneg ((ht.pos i).le) (pow_nonneg (div_nonneg (S.a_pos i|>.le) (S.a_pos k|>.le)) _))
omit y hT hj hW hb ha hB
local notation "J"=> C.path.levels.budget
variable (hV:Velour C (renal C.path.levels) r A)
include hV
lemma offset_lightness (p:ℕ):∀ᶠ i in atTop, 32*(fuga C.path.levels i) ≤ C.S.a p ∧ C.S.a (i+1)*((((J (i+1)).B^2+1+2*fusionSpan C.path.levels i):ℕ):ℝ)≤ C.S.a p:=by
   have hz:C.S.Gentle:=C.path.levels.fits.mesh
   have hh:= (Note.notes C.S (C.S.a p) (C.S.a_pos p)); refine ((Note.notes C.S 32 (by norm_num)|>.mills (fuchsia C hG hV)).outweigh hh (by norm_num)).and ?_
   have hv: N (fun i=> ((((J (i+1)).B)^2+1+2*fusionSpan C.path.levels i:ℕ):ℝ)) 0:=by
       unfold fusionSpan; push_cast; have he:N (fun i=> (((J (i+1)).B:ℝ))^2) 0:= ((briar C hG hV).scales hz|>.powerN 2).swapP (by norm_num); let ℓ (i:ℕ) : ℝ:= (C.S.block i).val
       have hk : N ℓ 0:=⟨fun i=>(by dsimp [ℓ]; positivity), C.path.levels.fits.mesh⟩
       have hv:N (fun i=> (((J i).B:ℝ))^2) 0:= ((briar C hG hV).powerN 2).swapP (by norm_num)
       exact (he.extra (Note.notes _ _ (by norm_num))).extra (((Note.notes C.S 2 two_pos).mills ((Note.notes _ _ zero_lt_one).extra ((hk.mills ((Note.notes C.S 512 (by norm_num)).mills hv)).swapP (by norm_num)))).swapP (by norm_num))
   exact ((Note.note_a C.S|>.scales hz).mills hv).outweigh hh (by norm_num)
end YM.MergeProof.Ribbons
