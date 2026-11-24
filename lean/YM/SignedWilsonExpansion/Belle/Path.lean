import YM.SignedWilsonExpansion.Dancer.Dial
/-! # Position projection. Manuscript's exact hierarchy value forces numerical D's
 on actual W. Uses Geometry assembled before requesting profiles. Root solve only in position;
 Light coupling meter *after* not independent photon. Uniform control Ret.Pair.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Belle
open FVA2 FVA2.Dframe FVA2.Scale
open Function MeasureTheory Filter Set Asymptotics XSpace XSpace.Structure1 Normalize
open MS MS.Menus MS.Puff MS.Land MS.High MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open Dancer Dancer.Drawing Commission
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d a b n:ℕ}{J I X:Type*}{L:Filter I}{t ν:ℝ}
namespace Path
-- always large enough horizon, finite lane, multiple outfits
variable (W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}(M:Speed.Quoted W K Y S)(s:G.Simple)
variable (V₀:Way G d)
def mote (a:ℕ)(x:Points n)(t:ℝ)(v: Tags G d n): ℂ:= ∑ i∈ Finset.range (a+1),(t:ℂ)^i* Jury.fxt V₀ x i v
lemma pollen (x:Stage n)(v: Tags G d n)(t:ℝ)(a:ℕ): mote V₀ a x.val t v= orbit V₀ a x t v:=by unfold mote; rw [atW]; simp_rw [Jury.exactC]
-- choose actual field branch.Real convention keeps MS pp weights.Leading tight
abbrev report (b:ℕ)(d:ℕ) (ν:ℝ)(t:ℝ): Prediction G d := ∑ i∈ Finset.range (b+1), t^i • (Reg.Faith.reports ν K Y d i) -- include Y explicit?
local notation "W₁"=> FVA2.Scale.Measure.start W K d
include s M
lemma neat (a:ℕ)(t:ℝ)(q:Tags G d n): ContDiffOn ℝ ∞ (fun x=>mote W₁ a x t q) (conf n):=by
   apply ContDiffOn.sum; intro i hi; apply contDiffOn_const.mul; exact fun x hx=> ( smoothP _ _ s M q i ⟨x,hx⟩ ).contDiffWithinAt
lemma smooth_c (v:Tags G d n)(i:ℕ): ContinuousOn (fun x=>Jury.fxt W₁ x i v) (conf n):= fun x hx=> ( smoothP W K s M v i ⟨x,hx⟩ ).continuousAt.continuousWithinAt
lemma nilReport : Reg.Faith.reports ν K Y d 0= Normalize.reference G d:=by
   ext1 n; ext1 x; ext1 v; rw [(Method.official s Y S ν W K M.toContract).exact]; change _= _ ; unfold Normalize.reference; -- inspect
   apply Test.apply_eq; intro y p; change Jury.fxt W₁ y 0 v =scene _ _ v; rw [show Jury.fxt W₁ y=_ from Jury.exactC W₁ ⟨y,p⟩]; exact DFunLike.congr_fun (Method.orderd0 s Y S W K M.toContract n (⟨y,p⟩:Stage n)) v
lemma images (ν:ℝ)(a:ℕ)(t:ℝ)(f:Test n)(v:Tags G d n) : f.applyTo (fun x=> mote W₁ a x t v)= report (Y:=Y) K a d ν t n f v:=by
   unfold Test.applyTo mote report; simp_rw [Finset.mul_sum,← mul_assoc, mul_comm (f _) ((t:ℂ)^_),mul_assoc]; rw [integral_finsetSum] -- simp callbacks
   · simp_rw [Finset.sum_apply,LinearMap.sum_apply,_root_.sum_apply]; simp_rw [integral_const_mul]; refine Finset.sum_congr rfl fun i _=> ?_; change (t:ℂ)^i * f.applyTo (fun x=>Jury.fxt W₁ x i v)= t^i • (Reg.Faith.reports ν K Y d i n f v); rw [Complex.real_smul,Complex.ofReal_pow,( Method.official s Y S ν W K M.toContract ).exact]
   intro i _; exact (f.smearing ( smooth_c W K M s v i )).const_mul _
-- survey left derivative. Strict
lemma retinal (ν:ℝ)(t:ℝ)(a:ℕ): (V.measure d).D (report (Y:=Y) K a d ν t )= (V.measure d).D (reference G d):=by
   rw [ report,map_sum,Finset.sum_eq_single 0,map_smul,nilReport W K M s,pow_zero,one_smul]; · intro i _ p; rw [map_smul,Method.washed s Y S ν W K M.toContract i p,smul_zero]
   simp
omit s M
section strict
variable {A:Screen G d} (D:Fray A)(H:A.Prepared)
variable {p:I→D.Bag}{v:I→MoveSpace G d}(hv:Tendsto v L (𝓝 0))(hp:Tendsto p L (𝓝 D.opening.1))(f:I→ℝ)
local notation "T"=> D.itinerary
include H hv hp
lemma firmness (h:(fun i=> T (p i,v i) - T (p i,0))=o[L] f): v=o[L] f:=by
   let A(i:I):= (p i,v i); let B(i:I):=(p i,(0:MoveSpace G d)); have hg:Tendsto (fun i=> (A i,B i)) L (𝓝 (D.opening,D.opening)):= (hp.prodMk_nhds hv).prodMk_nhds (hp.prodMk_nhds tendsto_const_nhds)
   let u:= ContinuousLinearMap.inr ℝ D.Bag (MoveSpace G d); have h'(i): A i-B i= u (v i):=by ext1 <;> simp [A,B,u]
   let X:= T ∘ A - T ∘ B; have ht (i:I):fderiv ℝ T D.opening (A i-B i) = v i:=by rw [h',show fderiv ℝ T D.opening (u (v i))= D.delta D.opening (v i) from rfl,D.unpin H]; rfl -- syntax fderiv
   have he:= (( D.fair.contDiffAt.hasStrictFDerivAt (by simp) : HasStrictFDerivAt T _ D.opening ).isLittleO ).comp_tendsto hg
   apply IsBigO.trans_isLittleO (g:=X) _ h; refine IsBigO.of_bound 2 (?_); filter_upwards [he.bound (show 0<(1/2:ℝ) from by norm_num)] with i hi
   change ‖X i - fderiv ℝ T D.opening (A i-B i)‖≤_ * ‖A i-B i‖ at hi
   rw [ht,h', show ‖u (v i)‖=‖v i‖ from by simp [u] ] at hi
   linarith [norm_sub_norm_le (v i) (X i), norm_sub_rev (X i) (v i)]
-- recruit primitive from horizon account
variable {P:I→Prediction G d}{v':I→Change G d}
omit hv hp
include H
lemma projected (h:Tendsto (guide G d ∘ v') L (𝓝 0))(p:Tendsto (fun i=> D.purse ( P i )) L (𝓝 D.opening.1)) (u:(fun i=> guide G d (A.D (recruit (stand ( v' i )) (P i))- A.D ( P i )))=o[L] f) : (guide G d ∘ v')=o[L] f:=by
    refine firmness D H h p f (u.congr_left (fun i=> ?_)); rw [ D.way,D.way,Function.comp_apply,Fray.box,Fray.box,map_zero,LinearEquiv.symm_apply_apply,stand0,map_sub]; rfl
end strict
end Path
end YM.SignedWilsonExpansion.Belle
