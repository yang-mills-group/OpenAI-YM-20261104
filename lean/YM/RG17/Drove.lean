import YM.RG17.Thimble
import YM.RG17.Workbox
import YM.RG17.Gild
/-! Costs of marching detector. 
No compact advice rechoosing with label arguments: uniform ANY key.
Unary threshold tests needed on only short chart of shrinking poly-β radius.
Pegs reaches costs as before. Same Ledger. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G){S:Table R.family.book}{f: Extraction.Order}
 {F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B} (fx:Flick R.family.path.levels)(W:Services R.family f S) (hz:Pegs D L)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "ν"=> Bid.gainChart R.family.path
include W
lemma rearWalk {t k m N p:ℕ}(u:R.family.label t) (hk:R.family.ref t ≤ k)(hm:k ≤ m)(hN:m ≤ N) : quota R.family t m N p u ≤ Real.sqrt (Bid.gainChart R.family.path m k)*quota R.family t k N p u:=by
    obtain ⟨K,r,V,hK⟩:=W.purchase
    have hr:Bid.Bank K R.family.path.levels:= hK.toTableTickets.system.costs.back
    induction m,hm using Nat.le_induction with
    | base=>simp only [Bid.gainChart,sub_self,mul_zero,Real.exp_zero,Real.sqrt_one,one_mul,le_refl]
    | succ i hi ih=>
      let s:= ((ι).params (i+1)).columns; let T:= (C|>.S.block i); let P:= Bid.puffs T
      let B:= (ι).clock.J (i+1); have hP :0≤P:= show 0 ≤ (T.val:ℝ)^(1/8:ℝ) from by positivity
      have hp:s ≤ Real.sqrt P:=by
         have he:100000*(K.K (B+1))^6*(1+s)^2 ≤ P:= hr i
         have hv : 1≤(K.K (B+1))^6:=one_le_pow₀ (K.prices _); have hh:1 ≤ s:= ((ι).params _).columns_ge
         have hz:s^2 ≤ P:=le_trans (b:=100000*(K.K (B+1))^6*(1+s)^2) (by nlinarith only [hh,hv,mul_le_mul_of_nonneg_right hv (sq_nonneg (1+s))]) he
         exact le_of_pow_le_pow_left₀ two_ne_zero (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hP]; exact hz)
      have hc: Bid.gainChart (C|>.path) (i+1) k=P*Bid.gainChart (C|>.path) i k:=by -- notation (C|>.path) maybe parse
        unfold P Bid.gainChart Bid.puffs T; rw [Schedule.scale_succ,Real.rpow_def_of_pos (by positivity),← Real.exp_add]; congr 1; ring
      rw [hc,Real.sqrt_mul hP,mul_assoc]; apply le_trans (show quota C t (i+1) N p u ≤ s * quota C t i N p u from R.makes.calibrated _ _ p ((hk.trans hi).trans ((Nat.le_succ i).trans hN)) |>.back i (hk.trans hi) hN ((R.family.factory t N p).terminal.symm u))
      exact mul_le_mul hp (ih ((Nat.le_succ i).trans hN)) (quota_nonneg _) (Real.sqrt_nonneg _)

include hz W
open Table
-- tolerance multiplicative on quota (apply at given fixed r and bound)
lemma frontWalk (t:ℕ): ∀ᶠ r in home,∀ u:ℝ,0<u→ ∀ᶠ i in L.lens,∀ x:R.family.label t, quota R.family t (L.level r) i.1 i.2 x ≤ R.family.S.a (L.level r)^t*u →
      ‖toFrame L t r (S.project t x)‖ ≤ (2*Lenses.bonus R.family t+1)*u:=by
   filter_upwards [hz.level.growing.eventually (Load.investors D W t),hz.level.growing.eventually_ge_atTop (C|>.ref t)] with r hr ht u hu
   apply refine_geometry; intro v b H' he hv
   let Q' := a (L.level r)^t*u; obtain ⟨l,hl,hL⟩:=quota_stop C R.makes ht
   obtain ⟨w,hw,hW,y,hY⟩:=finite_extract v (l*Q') (𝓛:=b) (by filter_upwards [hv,(large_mesh f (L.level r)).filter_mono (he.trans L.certified)] with i hh hr using (hL i.1 i.2 _ hr).trans (mul_le_mul_of_nonneg_left hh hl))
   let M: R.family.label t→L[ℂ] Free C t:= (toFrame L t r).comp ((S.project t).toContinuousLinearMap)
   have hq: ‖M y‖≤2*Lenses.bonus R.family t*u:=by
       change ‖(L.frame t r).symm _‖≤_; rw [hz.frame]
       refine (hr.2 w hW (le_trans hw (he.trans hz.along)) v y Q' (hv.filter_mono hw) hY).trans_eq ?_; have he:= R.family.S.a_pos (L.level r); unfold Q'; field_simp
   exact ⟨w,hW,hw, (M.continuous.continuousAt.tendsto.comp hY).norm.eventually (ge_mem_nhds (show ‖M y‖ < (2*Lenses.bonus R.family t+1)*u by linarith only [hu,hq]))⟩
end YM.RG17
