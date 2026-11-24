import YM.AllOrder.Haiku.Present
import YM.AllOrder.Haiku.Terrace
import YM.AllOrder.Plateau.Crop
import YM.AllOrder.Kinetic.Lily
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll
open AbsoluteSums Fare Shellac Work.G05
open Haiku.Coat Fire PertExtension.Series Radial -- order edit
open Response Ink Ink.Method Laurent Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable (A:ℕ→Atom G k) {σ C Z D β x:ℝ} (hs:0<σ)(hb: SumBudget (fun i=>(A i).budget σ) C)
local notation "E"=>Positions (Primary n G)
local notation "L"=>Kinetic.Port.exteriorL G n
section rainbow
-- ratio at grade-axis, valence shifts (e-k may be negative; book with both).
abbrev ratioW (p : ℝ) (e k: ℕ) : ℝ:=p^e*(p^k)⁻¹
def bend (b:ℝ)(x:E):= (Kinetic.Port.exteriorL G n).symm (b⁻¹ •x)
def bendL (b:ℝ): E→L[ℝ] Link G n:= b⁻¹ • (Kinetic.Port.exteriorL G n).symm.toContinuousLinearMap
lemma curve (b:ℝ) (x:E) : bend b x=bendL b x:= map_smul ..
lemma unbend (b:ℝ)(x:E)(h:0<b): b•(L (bend b x))=x:= by unfold bend; rw [ContinuousLinearEquiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ h.ne',one_smul]
lemma sail_eq (n:Side): turnSeries A (m:=n)= speak A n ∘ (Kinetic.Port.exteriorL G n):=rfl
lemma sail_back (n:Side): speak A n= turnSeries A ∘ ((Kinetic.Port.exteriorL G n).symm):= by rw [sail_eq]; exact funext fun x=> by simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
include hb hs
local notation "D'"=> turnSeries A (m:=n)
lemma sail_tip (v:Link G n)(j:ℕ): Radial.jet D' j v=Radial.jet (speak A n) j (L v):= by rw [sail_eq]; apply Kinetic.pivot ((Kinetic.Port.exteriorL G n).toContinuousLinearMap); rw [sail_back]; exact ((map_zero (L).symm).symm ▸ (turns_analytic A hs hb).contDiffAt).comp _ (L).symm.contDiff.contDiffAt
-- `eta=r` largest term retained, `e` age, given `k` arity
lemma sail_full (b : ℝ)(hg:0<b)(e r:ℕ)(he:e≤r)(x:E):
 ∑ j∈ Finset.range (r+1), b^j * trade e A j n (bend b x)= ratioW b e k * blockTaylor (r-e+k) (speak A n) x:= by
 let Y:= turnSeries A (m:=n); have hh(i:ℕ)(hi:i<k) : Local.Pure.chip (speak A n) i (L (bend b x))=0 := by change jet _ i _=0; rw [← sail_tip A hs hb]; unfold Radial.jet; rw [(rays_jet (turns_analytic A hs hb) _).1 (turns_low A hs hb) i hi]; simp
 nth_rw 2 [← unbend b x hg]; rw [Local.Pure.bill_insert, show r+1=e+(r-e+1) by omega,show r-e+k+1 = k+(r-e+1) by omega,sum_range_add _ e,sum_range_add _ k]; -- erase zeros derive
 have he₁ : ∑ i∈ Finset.range e,b^i*trade e A i n (bend b x)=0:= Finset.sum_eq_zero fun i hi=> by rw [trade,if_neg (not_le_of_gt (Finset.mem_range.mp hi))]; simp
 have he₂ : ∑ i∈ Finset.range k,b^i*Local.Pure.chip (speak A n) i (L (bend b x))=0:= Finset.sum_eq_zero fun i hi=> by rw [hh i (Finset.mem_range.mp hi),mul_zero]
 rw [he₁,he₂,zero_add,zero_add,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [trade,if_pos (by omega),sail_tip A hs hb]; -- align
 rw [show e+i-e+k=k+i by omega]; unfold ratioW; change b^ _ * _ = _ * (b^_ * Radial.jet (speak A n) (k+i) _); rw [pow_add,pow_add]; field_simp
end rainbow
section prune
variable {V : Type}{Y:V→ℝ}{T: Repertoire V G} {X : Theatre G V}(H:Spliced Y X T (N+1))
omit hb hs
-- simpler function equality off(F) minus polynomial
abbrev played (i:V)(b:ℝ)(e k:ℕ) (r:Fin (e+1))(x:E):= ratioW b e (r.val+2)* blockTaylor (k-e+(r.val+2)) (speak (T e r i) n) x -- invalid T implicit? ok
abbrev outlay (n:Side)(i:V)(b:ℝ)(R:ℕ) (x:Positions (Uniform.Primary n G)):=∑ e∈ Finset.range (R+1), ∑ r:Fin (e+1), played (T:=T) i b e R r x
include H
lemma recital (i:V)(b:ℝ)(u:ℕ)(hu:u≤N)(hg:0<b)(x:E) : ∑ j∈ Finset.range (u+1), b^j*(crowd T (N+1)) i j n (bend b x) = outlay (T:=T) n i b u x := by
 let f (e:ℕ)(r:Fin (e+1))(j:ℕ) := b^j*trade e (T e r i) j n (bend b x)
 simp_rw [crowd,Haiku.Coat.reel,Finset.sum_apply,Finset.mul_sum]
 rw [Finset.sum_comm]; have he : ∑ e∈Finset.range (N+1), ∑ j∈ Finset.range (u+1),∑ r:Fin (e+1),f e r j = ∑ e∈ Finset.range (u+1),∑ j∈ Finset.range (u+1),∑ r:Fin (e+1),f e r j:= by
    symm; apply Finset.sum_subset (Finset.range_mono (by omega)); rintro e _ hT; apply Finset.sum_eq_zero fun j hj=> ?_; apply Finset.sum_eq_zero fun r _=>?_; simp_rw [f,trade, if_neg (show ¬e ≤ j from lt_of_lt_of_le (Finset.mem_range.mp hj) (by simpa using hT)|>.not_ge),Pi.zero_apply,mul_zero]
 refine he.trans (Finset.sum_congr rfl (fun e he=>?_)); rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r _; have h: e < u+1:= Finset.mem_range.mp he; obtain ⟨a,ha,F,h'⟩:= H.age e (by omega) r; exact sail_full _ ha (h'.2 i|>.1) b hg e u (by omega) x
lemma lit (i:V)(b:ℝ)(r:ℕ)(he:r≤N)(hg:0<b) : Shellac.off (fun x:E=> ∑ j∈ Finset.range (r+1), b^j*X i j n (bend b x))= Shellac.off (outlay (T:=T) n i b r) := by
 ext1 x; change (∑ j∈ Finset.range _, _) - ∑ j∈ Finset.range _,_=outlay _ _ _ _ _ -outlay _ _ _ _ _; rw [← recital H i b r he hg x, ← recital H i b r he hg 0,← Finset.sum_sub_distrib,←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j hj; rw [← mul_sub, ← mul_sub]; apply congr_arg; have hv := Finset.mem_range.mp hj; have hq: X i j n (bend b x)-crowd T (N+1) i j n (bend b x)=X i j n (bend b 0)-crowd T (N+1) i j n (bend b 0):= H.project i n j (by omega) _ _; linarith only [hq]
end prune
end YM.AllOrder.Plateau
