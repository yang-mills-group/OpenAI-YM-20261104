import YM.RG16.Unmasked.Purchased
/-!
# Budget transfer to the intrinsic OPE report

`literal` fits via GermGraph; `funds` on the whole replicated Z. Reading the
moment / whole λ coefficient after contraction, must price their DIFFERENCE
in the physical root. Otherwise growth from grade inverses could eat the
spatial decay. This cost is paid on the **same normalization** (seam).
Also preserve estimate for use BEFORE testing the root -- needed to anchor
linear operations in perturbation theory. We keep corners on the actual Mesh
levels (no necessary alignment with a hypothetical Hermitian measuring Gram
beyond what `R` specifies on this Q). The price's most useful feature: no
entry of the independent A report enters the exact bound here, so one may use
an all-order answer calculated on a modest-per-rep FG budget on this *same*
history without conjoining it on all copies or postulating that the requisite
large-copy FG variants have been paid.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG16.Literal
open Function Set Filter MeasureTheory OPE Lattice Wilson RG Source Overlay Bid MergeProof Accent
open Ribbons ManyCopies Cells Extra.Histories Push.Local
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
variable {G : Gauge} (C: Family G) (hG:G.Simple){W r D} (L:Package C W r D)
local notation "P" => C.path.levels
local notation "σ" => C.S.scale
local notation "F" => C.labels.level
open Trace.Physical.GermGraph

variable (h:C.Makes) {I : Type} [Fintype I][DecidableEq I] [Nonempty I] (d : I→ℕ)(p N b k e J u:ℕ)
  (Gm : ℕ→ℝ) (hGm : RateIs atTop C.S.scale Gm 0)
set_option quotPrecheck false
local notation "Z" => (C.labels.level e)
local notation "F₀" => (C.factory e N p)
section
variable (hu: Opened C e u p) (hm:Stock.Tabs.opens C.path.levels 1 J u)
    (hJ:C.ref e ≤ J) (hN:u<N)
local notation "Y" => center C.S p (hm.1.trans hN.le) 0
include L hJ h
lemma fixed_tiling_charge (w:C.label e) :
    (Y).rootTest (C.beta N p) (C.O N p w 0) ≤ ‖w‖ *
       Real.exp (expense C ((C.labels.level e).extra+1:ℕ) J u e) := by
    let f := F e; let v:= w; let a:ℝ:= (f.extra+1:ℕ)
    let T:= Y; let c := Complex.ofReal ‖w‖
    let m:= (C.linearO N p e 0).mk' _
    have h0:0<a:=Nat.cast_pos.mpr (Nat.zero_lt_succ _)
    by_cases hz:w=0
    · rw [hz,norm_zero,zero_mul,show C.O N p (0:C.label e) 0=0 from m.map_zero]; simpa using (Next.Extract.root_smul T (C.beta N p) (G:=G) (0:Config G (C.side N p)→ℂ) 0).le
    have h₀ : 0<‖w‖:= norm_pos_iff.mpr hz
    have hp:0<‖c‖:= by simp [c,h₀]
    have hc:‖c⁻¹ • w‖=1:= by
       rw [norm_smul, norm_inv]; simp only [c,Complex.norm_real,norm_norm]; exact inv_mul_cancel₀ h₀.ne'
    have hv:= tent C N u J p e (c⁻¹ • w) a h0 L.tabs h L.system.costs L.system.back hm hJ hN
       (le_trans (size_le_norm ..) (by rw [hc,mul_one]))
    rw [show C.O N p (c⁻¹ • w) 0 = c⁻¹ • m w from m.map_smul .., Next.Extract.root_smul] at hv
    rw [norm_inv, show ‖c‖=‖w‖ from by simp [c],← div_eq_inv_mul] at hv
    exact (div_le_iff₀' h₀).mp hv

include h hm hJ L
lemma cylinder_cost (ho:∀ p,Opened C e u p) :
    ∃ K : ℝ, 0≤ K ∧ ∀ N p,∀ hN:u<N,∀ z:C.label e,
        (center C.S p (hm.1.trans hN.le) 0).rootTest (C.beta N p) (C.O N p z 0) ≤
         K * (mCost C e N p u ((C.factory e N p).terminal.symm z)) := by
   obtain ⟨c,hc,h⟩:= Next.UVStress.quota_stop C h (ho 0).post
   let g:= Real.exp (expense C ((C.labels.level e).extra+1:ℕ) J u e)
   have hg:0<g:=Real.exp_pos _
   refine ⟨c*2*g,mul_nonneg (mul_nonneg hc zero_le_two) hg.le,?_⟩
   intro N p ht z
   have hp:= (size_gap e N p u (‹C.Makes›) (ho p) ht.le ((C.factory e N p).terminal.symm z)).2
   have hv:= fixed_tiling_charge C L (‹C.Makes›) p N e J u hm hJ ht z
   let P₀:=mCost C e N p u ((C.factory e N p).terminal.symm z)
   exact hv.trans ((mul_le_mul_of_nonneg_right ((h _ _ _ ht.le).trans (mul_le_mul_of_nonneg_left hp hc)) hg.le).trans_eq (show c*(2*P₀)*g=_ from by ring))
end

lemma Funds.pay {dR E w : ℝ} {f:Cut C N p} {hj:J ≤ u}{hu:u ≤ b}{hi:b ≤ N}
    {hh:Opened C e u p} {z:C.label e} {q: store C e p b}(x:Funds C h p N b e J u E dR w f hj hu hi hh z q) {A:ℝ}(ha:0 ≤ A)
    (hm:∀ y : C.label e, let M:=center C.S p (hj.trans (hu.trans hi)) 0;
       Interior (M.chamber 0) (C.O N p y 0) ∧ M.rootTest (C.beta N p) (C.O N p y 0) ≤ A*mCost C e N p u ((C.factory e N p).terminal.symm y)) :
    let Z':= topReport C N p e h u hh (hu.trans hi) f
    let W : Config G (C.side N p)→ ℂ:= f - C.O N p ((C.factory e N p).terminal Z') 0
    let X₀:=center C.S p (hj.trans (hu.trans hi)) 0
    Interior (X₀.chamber 0) W ∧ X₀.rootTest (C.beta N p) W ≤ 2*(stakes C J u/w)+A*(E/gainChart C.path b u) := by
   intro Z' W X₀; let m:= (C.linearO N p e 0).mk' _
   let l:=(C.factory e N p).terminal
   let v := z - l Z'
   have hf := hm v
   have hW : W=(f - C.O N p z 0)+ C.O N p v 0 := by
      rw [show C.O N p v 0= m z-m (l Z') from m.map_sub ..]
      unfold W; change f - m (l Z') = f - m z + _; abel
   have hs : mCost C e N p u (l.symm v) ≤ E/gainChart C.path b u := by
     let g:= fitting e N p u h hh (hu.trans hi)
     calc _ = mCost C e N p u (Z'-l.symm z) := ?_
          _ ≤ _ := x.currency
     change (F e).coeffSize (g _)=(F e).coeffSize (g _)
     unfold v; rw [map_sub,l.symm_apply_apply,map_sub,map_sub,←neg_sub (g Z') (g (l.symm z)),count_neg]
   rw [hW]; exact ⟨Interior.plus x.inview hf.1,le_trans
       ((seamless h N p).semi X₀ _ _ x.inview hf.1)
       (add_le_add x.packing (hf.2.trans (mul_le_mul_of_nonneg_left hs ha))) ⟩
end YM.RG16.Literal
