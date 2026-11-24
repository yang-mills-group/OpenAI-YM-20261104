import YM.OPE.Compatible.Ticks.Inherit
/-!
# Allocate an entire long or short line, after a union.

Only pay after the budgets are known; move the chosen Stems, not merely
those available. At uppermost root, the short, empty line keeping
Blade ready for rotation back into a Frame is used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V:Type}[Fintype V][DecidableEq V] (P:Ensemble V)
variable {N p k j n b d i:ℕ}{E o:Track C.path V p}
-- joined Spine price. Drawing root still needs full exact tag. v top purchase, η≥ headway(r>=m) controls aligned path.
-- always loses a beta polynomial no matter if needed or not

def sash (C:Family G)(m:ℕ) := let x:=β C m; let a:= x^MergeProof.winter G 0; (1024*x*a*a)⁻¹
lemma sash_hi (C:Family G)(m:ℕ): sash C m ≤ 1/128:=by
   let x:=β C m; let a:= x^MergeProof.winter G 0; have hp:1<x:=β_one ..; have he: 1≤a:=one_le_pow₀ hp.le
   have hz: (128:ℝ) ≤ 1024*x*a*a:=by have hh:= mul_le_mul_of_nonneg_left he (show 0 ≤1024*x*a by positivity); nlinarith only [hp, he, hh]
   exact (inv_anti₀ (by norm_num : (0:ℝ)<128) hz).trans_eq (one_div _).symm
lemma sash_pos (C:Family G)(m:ℕ): 0 < sash C m:=by unfold sash; dsimp only; have he:=β_one C m; positivity
include A
lemma saved (hG:G.Simple)(hi:C.ref 0≤ i): sash C (i+1)*(24*(1+(C.path.levels.params i).columns)*(4*β C (i+1)))≤ fly C.path.levels 0 i:=by
    let x:=β C i; let y:=β C (i+1); let b:= MergeProof.winter G 0; let W:=y^b; have he: 1<W ∨ 1=W:= ((one_le_pow₀ (β_one ..|>.le)): 1≤ W).lt_or_eq; have hw:1≤ W:= le_of_lt_or_eq he; let Q:=(C.path.levels.params i).columns; have h: Q ≤ W:= (columns_save A _ _ hi).trans (pow_le_pow_left₀ (β_pos ..|>.le) ((β_increases hG).monotone i.le_succ) _)
    refine le_trans (?_ : _ ≤ fly C.path.levels 0 (i+1)) (fly_le hG 0 i (i+1) i.le_succ); change (1024*y*W*W)⁻¹*(24*(1+Q)*(4*y))≤ W⁻¹; have hh:0 < y:=β_pos ..
    field_simp; nlinarith
-- b in formulas head weight ν∗ throughout path, adjust at lower stop always factor a_cut/a_finish if nonaligned steps. midpoint `stops` k..j marks horizon to resume alignment. rough segment spans top k' (j≥k') through k. when midpoint=j no conversion. Include Blade at j for root.
lemma new_line (hg:G.Simple)(h:C.Makes)(hi:C.ref 0 < k)(hk:k ≤ i)(hz:i ≤ j)(hN:j≤N)(hm:Migrating C.path k p j E)(hM:Migrating C.path i p j o)(hy:∀ i',k ≤ i' → i'< j→ (C.path.levels.clock.op i' p).ratio.parent ∘ o (i'+1)=o i')
    (hω:∀ a,k ≤ a→ a ≤ j→ ∀ x:V, x≠P.v→ o a x=affine (P.move x).1 (E a x) (o a P.v))
    {U:Stem V G (C.S.side j p)}{v:ℝ}(hw:0<v)(hW:U.home=o j)(hX: Marked (C.path.rep N p j) (E j) P U)
    (hB:Blade (C.path.rep N p j) (U.home P.v) (U.oil P.v) (profile (C.path.rep N p j).activities (U.gas P.v)) 0 (4*(1/v))):
    ∃ L:Line A P N p k j b E o, L.X j=U ∧ L.w j=(sash C j)*v/2 ∧ L.w j ≤ v ∧ L.w k=Run.Below C.path ((sash C j)*v/2) i k:=by
   let w:=(sash C j)*v; have hw': 0<w:= mul_pos (sash_pos C j) hw; have hw₀:w ≤ v/128:= (mul_le_mul_of_nonneg_right (sash_hi C j) hw.le).trans_eq (by ring); have hu:w/2 ≤ v:=by linarith only [hw,hw₀]
   have h_f: 0 < w/2:= by linarith only [hw']
   rcases Nat.eq_or_lt_of_le hz with rfl|hv
   · have he : 4*(1/v) ≤ 1/(2*(w/2)):=by
       rw [mul_div_assoc' 4 1 _,mul_one] -- inspect
       apply (div_le_div_iff₀ hw (by linarith only [hw'])).2; linarith only [hw₀,hw]
     obtain ⟨L,h_L,hG⟩:= Line.roll_below (b:=b) A P h hi.le hk hN hm 0 hX (hB.more he) (by simp) h_f hW.symm hy
     exact ⟨L,h_L,congr_fun hG _|>.trans (Run.below_main _),(congr_fun hG _|>.trans (Run.below_main _)).le.trans hu,congr_fun hG _⟩
   cases j with
   | zero=>omega
   | succ j=>
      let S:= 4*(1/v); have hi':i ≤ j:=by omega
      have hj:C.ref 0 ≤ j:=(hi.le.trans hk).trans hi'; have hh : w* (24*(1+(C.path.levels.params j).columns)*(β C (j+1)*S)) ≤ fly C.path.levels 0 j:=le_trans (le_of_eq (b:=_) ?_) (saved A hg hj)
      swap; · unfold w S; field_simp
      let Q:=(C.path.levels.params j).columns; let c:=fly C.path.levels 0 j; have hd:1 ≤ Q:= (C.path.levels.params j).columns_ge
      have hζ:c ≤1:= by rw [show c= _ from fly_eq C 0 j]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (β_one ..|>.le))
      have hs:β C (j+1)*S>0:=mul_pos (β_pos ..) (mul_pos (by norm_num) (by positivity)); have hs':0<S:=mul_pos (by norm_num) (by positivity)
      have hx : 24*(w*(β C (j+1)*S)) ≤ 1:= le_trans (le_trans ?_ hh) hζ; swap
      · apply le_of_sub_nonneg; nlinarith only [mul_nonneg (mul_nonneg hw'.le (show 0≤ Q from zero_le_one.trans hd)) hs.le]
      have h8:(4*w*S)≤1:=by have ht:S ≤ β C (j+1)*S:=le_mul_of_one_le_left hs'.le (β_one ..|>.le); have hh:=mul_le_mul_of_nonneg_left ht hw'.le; linarith only [hh,hx]
      obtain ⟨X,hP,hN',hz⟩:= received A P hj hN hg h hs' hw' h8 (by linarith only [hx]) hh (hi.le.trans hk) hi' hX hB hW.symm ⟨fun i hi hx=> hm.mare _ (hk.trans hi) hx⟩ hM (fun x hi hx=> hω x (hk.trans hi) (hx.trans j.le_succ))
      obtain ⟨c,hc,hq⟩:=hz i (lt_of_lt_of_le hi hk) le_rfl hi'
      let L:Line A P N p i (j+1) b E o:=⟨X,fun _=> w/2,hP.credit (fun _ _ _=> h_f) (fun _ _ _=>by linarith only [hw']), fun q _ _=> le_mul_of_one_le_right h_f.le (one_le_pow₀ (β_one ..|>.le))⟩
      obtain ⟨T,hT,hB⟩:= Line.roll_below (b:=b) A P h hi.le hk (le_trans hi' (Nat.le_trans j.le_succ hN)) ⟨fun i hi hk=>hm.mare _ hi (lt_trans hk hv)⟩ c (hP.marks i le_rfl hv.le) (by simpa only [show 2*(w/2)=w from by ring] using hq) ((mul_le_mul_of_nonneg_right (by change w/2 ≤w; linarith only [hw']) (norm_nonneg _)).trans hc) h_f (hP.steers _ le_rfl hv.le|>.symm) (fun q hk ht=> hy q hk (ht.trans hv)) -- remove
      obtain ⟨Z,hZ,hE⟩:= T.continueW L hT (congr_fun hB _|>.trans (Run.below_main _)); have he':Z.w (j+1)=w/2:= (hE (j+1) (by omega)).1
      exact ⟨Z,((hE _ hv.le).2).trans hN',he',he'.le.trans hu,(hZ k hk).1.trans (congr_fun hB k)⟩
end YM.OPE.Allot
