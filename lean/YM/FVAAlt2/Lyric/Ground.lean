import YM.FVAAlt2.Lyric.Keeper
import YM.FVAAlt2.Block.Census
import YM.FormalOPE.RG10.Occupied
import YM.Comparison.RG02.Laplace.Inside
/-! # bank normalization cooked on the entire torus, marker/coupling conventions. Rigidity for one mark uses logMarker on ALL with quiet distinction unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Lyric
open Function Finset Filter Set MeasureTheory Matrix Metric
open Marker Multi Order Assembly Laplace Order
open YM.Extra.Trajectories FormalOPE.RG10 FormalOPE.RG10.Word PowerSeries
open PertExtension PertExtension.Series
open scoped Topology Classical BigOperators ContDiff Matrix PowerSeries
variable {V:Type}[DecidableEq V][Fintype V] {R:Census V}{r k e:ℕ}
variable {X:Grade R r}(hX:Order.Symmetric X)(h:UnitLeading X)
open RegulatorIR.FVAAlt2 RegulatorIR.Diagram.Formal
variable (R) in
lemma real_work (w:PowerSeries ℝ)(hw : coeff 0 w=0): Order.series R r (realCurve R (fun i=> coeff i (expo w)))=Marker.Poly.pass (Order.series R r (realCurve R (fun i=> coeff i w))) := by
    let u(i:ℕ)(x:ℝ) := coeff i w
    have hu(i:ℕ): Radial.expsum u i i 0=coeff i (expo w) :=( RegulatorIR.FVAAlt2.Lyric.Capacity.painter (r:=i) (fun j _=> (show u j 0=_ from rfl)) le_rfl ).symm
    rw [← _root_.funext hu]; exact Assembly.real_pass u (funext fun _=>hw) 0

include hX
local notation "Δ"=> detail X R.quiet
lemma fastens (u:PowerSeries ℝ) (he: ∀ i≤r,Δ i=(↑(coeff i u):ℂ)) : Order.denominator X=Order.series R r (Assembly.realCurve R (fun i=>coeff i u)):=by
    unfold Order.denominator; apply (sym_coeff _ _ (hX.vacant) ⟨_,rfl⟩).2; intro i hi; ext s; rw [observation _ _ _ hi,realCoeff,beads,observe_bottom,pure_marks]; split_ifs with hv; exact he _ hi; rfl
lemma notice {u:PowerSeries ℝ}(h : coeff 0 u=0) (he: ∀ i≤r,Δ i=(↑(coeff i (expo u)):ℂ)) : logVac X=Order.series R r (realCurve R (fun i=>coeff i u)):=by
    rw [logVac, fastens hX _ he, real_work R u h ]; apply Cumulants.connected_pass; rw [ ← Join.pair_quiet,polarization]; change _ * ((PowerSeries.coeff 0 (realCurve R _)).part R.quiet)=_; rw [realCoeff,beads,h,Complex.ofReal_zero, if_pos rfl,mul_zero]
variable (s:R.Mode)
include h
-- recurrence (multilinearity at each independent-coefficient level): permits real prospects per mark instead of assuming every joint mark.
lemma exposes {u v:PowerSeries ℝ}(h₀:coeff 0 u=1)(hu: ∀ i≤r,Δ i=(↑(coeff i u):ℂ)) (hv: ∀ i≤r,detail X s i=(↑(coeff i (u*v)):ℂ)) : ∀ i≤r, detail (Order.ratio X) s i=(↑(coeff i v):ℂ) :=by
    let Y:=Order.ratio X; have hY:= sym_ratio h hX; obtain ⟨g,hg⟩:=hY; -- check
    have ht: X=Order.series R r (realCurve R (fun i=> coeff i u) * g):=by rw [map_mul, ← fastens hX u hu,hg,recovers h]
    intro i; induction i using Nat.strong_induction_on with
    | _ i ih=>
       intro hi
       let h₁:=hv i hi
       -- since h mutable
       replace h₂:=h₁; rw [ht] at h₂; unfold detail at h₂; rw [ ←hg, detail, observation _ _ g hi ]; rw [observation _ _ _ hi, coeff_mul,Marker.Poly.part_sum,coeff_mul, Complex.ofReal_sum] at h₂
       simp_rw [realCoeff, Marker.Poly.product_bead, Marker.Poly.part_smul,Complex.ofReal_mul] at h₂
       let f(k:ℕ):= (coeff k g).part s; let S:=antidiagonal i
       have hp:(0,i)∈S:= mem_antidiagonal.mpr (zero_add i)
       have he: ∑ p∈ (S.erase (0,i)),(↑(coeff p.1 u):ℂ)* f p.2=∑ p∈S.erase (0,i),(↑(coeff p.1 u):ℂ)*(↑(coeff p.2 v):ℂ):=by
          refine sum_congr rfl (fun p hx=>?_); obtain ⟨hx,hy⟩:= mem_erase.mp hx; have hp:=mem_antidiagonal.mp hy; have hh:p.2 < i:= by obtain ⟨p,q⟩:=p; by_contra! hq; exact hx (Prod.ext (by dsimp only; omega) (by dsimp only; omega));
          have hq:= ih p.2 hh (hh.le.trans hi); rw [← hg, detail, observation _ _ g (hh.le.trans hi)] at hq; rw [show f p.2=_ from hq]
       change ∑ p∈S,(↑(coeff p.1 u):ℂ)* f p.2= ∑ p∈S,(↑(coeff p.1 u):ℂ)*(↑(coeff p.2 v):ℂ) at h₂
       rw [← Finset.sum_erase_add _ _ hp, he, ← Finset.sum_erase_add (f:=fun p : ℕ × ℕ=> (↑(coeff p.1 u):ℂ)*(↑(coeff p.2 v):ℂ)) _ hp, add_right_inj] at h₂
       change f i= (↑(coeff i v):ℂ); simpa [h₀] using h₂
-- rigging for singleton output measures/reratio through *whole* bank. 
lemma logo (a:V)(he:e≤r) : detail (Order.ratio X) (R.fire a) e=detail (Order.logMarked X) (R.fire a) e:=by
    let Y:=Order.ratio X; have hY:= sym_ratio h hX; let V':= Order.collect Y; have hx:Order.series R r V'=Y:= recollect hY
    have ht:Order.denominator Y=1:= ratio_pure h; have hp: vac R V'=1:=by
       ext1 i; rw [vac_eq,unfold_see]; unfold V'; rw [Order.collect_coeff]; have hu:( observe R r Y i ).part R.quiet=( observe R r (Order.denominator Y) i).part R.quiet:=by rw [Order.denominator,observe_bottom,pure_marks]; simp; -- rfl
       rw [hu,ht, ← map_one (Order.series R r)]; by_cases hv:i ≤ r; swap
       · unfold Order.observe; rw [if_neg hv, coeff_one, Marker.Poly.part_nil,if_neg (by omega)]
       rw [observation _ _ _ hv,coeff_one,coeff_one]; split <;> simp
    unfold Order.logMarked; change _= detail (connected Y) _ _
    change detail Y _ _=_; rw [← hx, ← YM.FVAAlt2.Block.series_log _ _ V' (by rw [boot,hp];simp)]; unfold detail; rw [observation _ _ _ he,observation _ _ _ he]; rw [← Word.unfold_see _ V', ← Word.unfold_see _ ( Word.logWord V' ), Word.alone V' hp]

end YM.Comparison.RG02.FVAAlt2.Lyric
