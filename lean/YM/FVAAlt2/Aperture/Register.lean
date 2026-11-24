import YM.FVAAlt2.Aperture.Counter
/-!
# Full Periodic Aperture Register: actual-model matcher ordinary coefficients in rescaled t-era

Output column-read at χ UnitCost before pose. Shifts VERY signs and normalization constants even for U=1. Exact through positive profile LEG. Tapes.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure Actual
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V] {R:Census V}(W:Bulk.Colors R G f)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ" => C.enter
local notation "H" => F.Slice G
local notation "Q" => K.covariance F w
open Classical
variable (t:ℝ) (x:fieldDir G c 1)
local notation "ζ"=> Bulk.translated K F x
open Laplace PertExtension.Series.Tested Symmetry Symmetry.Ribbon Trade LocalScript Moving Moving.Shift Moving.Path
variable (A:Set (F.Slice G))
variable (r:ℕ)[Fintype V] (D: BudgetPoint) (s:R.Mode)
local notation:max "v_" g:max=> unitx C x g
local notation "φ"=> entry K F w C x
local notation "u'"=> unitx C x
local notation "P'" => fuse R r (fare K F w C W x r)
local notation "Ψ" => bank K F w C W x r
local notation "Σ'"=> LocalScript.signal K F w 0 W C r x
local notation "ξ" => spring R r (entry K F w C x)
lemma billed {f : ℝ→ℂ}(h:Bill r f): Bill r (f ∘ C.enter):= by
    obtain ⟨u,hu,H'⟩:=h; refine ⟨u*2^r,by positivity,?_⟩
    filter_upwards [C.forward.eventually H', (C.rating_rises.mono_left (show along≤𝓝 0 from nhdsWithin_le_nhds)).eventually (gt_mem_nhds (show (1:ℝ)<2 by norm_num)),Tested.eventually_pos,C.bright.filter_mono (show along≤𝓝 0 from nhdsWithin_le_nhds)] with g hg hh hm hb
    change C.rating g <2 at hh
    apply hg.trans; rw [ UnitCost.enter, mul_pow ]; have H₁:= pow_le_pow_left₀ hb.le hh.le r; rw [mul_comm (g^r), ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H₁ hu) (by positivity)
variable (hW:Well W) (B:Bed)(hB: YM.FVAAlt2.Period.Rent.Right p P f B)
include hW D
lemma proffers : ∃ Z∈𝓝 (1:F.Slice G), IsOpen Z ∧ ∀ A:Set (F.Slice G), A⊆Z → MeasurableSet A → A∈𝓝 1 → Trial (detail P' s) (fun t=> (tale K F w C W t x A).part s) r:=by
    let Y' : ℝ→X:= unitx C x ∘ C.inverseCurve.enter
    have hv : glows Y':=(show ContDiffAt ℝ ω u' (C.inverseCurve.enter 0) by rw [C.inverseCurve.borne]; exact timeUnit C x ).comp _ C.inverseCurve.here
    obtain ⟨Z,hZ,H₁,H₂⟩:= Symmetry.accost K D F w (Y' 0) Y' W 0 r s hW (hv.continuousAt.mono_left (show along≤𝓝 0 from nhdsWithin_le_nhds)); refine ⟨Z,hZ,H₁,fun A hi hp hl=>?_ ⟩
    let V'(g:ℝ):= (portal K F w 0 W (Y' g) (fun _=>A) g).part s-(value (g:ℂ) (Fk K F w W (Y' g) r)).part s
    have hs: Bill (r+1) V':= H₂ _ ⟨A,hl,Eventually.of_forall fun _=> ⟨ hi,hp,Set.Subset.refl _⟩⟩
    let U₁(t:ℝ):= (value (t:ℂ) (fare K F w C W x r t)).part s
    have hu: Trial (detail P' s) U₁ r:= trial_flow (a:=Moving.Path.motion U₁) (Moving.Path.ordinary ( (price_b K F w C W x r s).of_le le_top) r) (fun i hi=> Moving.Shift.valued (agency K F w C W x r) (worthy K F w C W x r) hi)
    have hx:= bill_mul (Moving.Path.ordinary ((entryT K F w C x).of_le le_top)|>.bounded) (billed C (r+1) hs);rw [Nat.zero_add] at hx
    change Bill _ (φ*(V'∘C.enter)) at hx; unfold Trial; refine Laplace.bill_congr ?_ (bill_add hx hu)
    filter_upwards [C.bright.filter_mono (show along≤𝓝 0 from nhdsWithin_le_nhds),Tested.eventually_pos,C.rightInverse.pairs.filter_mono (show along≤𝓝 0 from nhdsWithin_le_nhds)] with t hv ht hh
    dsimp only [Function.comp_apply,id_eq] at hh
    have hz:Y' (ρ t)= v_ t:=congr_arg u' hh
    change (φ t * V' (ρ t))+(U₁ t - _)=(tale K F w C W t x A).part s- _
    unfold V' U₁; rw [hz,forecast,known_convention K F w C W t x r s hv,portal_price K F w C W t x A ht hv, Marker.Poly.part_smul]; ring
include hB
lemma absolute_price : Ψ=ξ*Σ':=by
    have ht : Ψ=P':= by
       apply (sym_coeff _ _ ( Aperture.symmetric .. ) (fuse_symmetric (worthy K F w C W x r)) ).2; intro i hi; apply Marker.Poly.ext; intro s
       obtain ⟨U,hU,hV,hv,hm⟩:= permits K F w C W x D s hW B hB r; obtain ⟨Z,hZ,hp,hz⟩:= proffers K F w C W x r D s hW
       let A:=U∩ Z; have hh:A∈𝓝 1:= inter_mem hU hZ; have hs: MeasurableSet A:= (hV.inter hp).measurableSet
       exact trial_gap (hm A Set.inter_subset_left hs hh) (hz A Set.inter_subset_right hs hh) _ hi
    rw [ht]; exact fuse_prod (heat_seen R r φ (entryT K F w C x)) ((accounts K F w W r).describes C 0 r x)
lemma line_ordinary : Order.ratio Ψ=Order.ratio Σ':=by
    symm; apply Order.ratio_unique (units ..); rw [absolute_price K F w C W x r D hW B hB]; unfold denominator; rw [map_mul, show bottom R r ξ=ξ from Ribbon.sprouted .., mul_assoc,show bottom R r Σ'* Order.ratio Σ'= Σ' from recovers ( (accounts K F w W r).rolls C 0 r x )]
lemma posts_mark (i:ℕ)(hi:i≤r): detail (logMarked Ψ) s i = Adjacent.born (Symmetry.Orbit.words K F w W r s) C 0 r i x:=by
   unfold logMarked; rw [line_ordinary K F w C W x r D hW B hB]; have he:= recount K F w (0:V→ℤ) W C s r x i hi; simpa only [logMarked,markDebt,Pi.zero_apply,sum_const_zero] using he
-- Accessor for Spring (Orbit.pay private)
omit hB hW D in
lemma spring_mark (F:ℝ→ℂ)(h:smooth F)(i:ℕ)(hi:i≤r): detail (spring R r F) R.quiet i=motion F i:=by
    have ht: ∀ t:ℝ,(value (t:ℂ) (Ribbon.heat R r F t)).part R.quiet=F t:=by
       intro t; unfold heat; rw [show value (t:ℂ) (F t • _) = F t • value (t:ℂ) (1:Grade R r) from (valueL R r _).map_smul _ _, Marker.Poly.part_smul];
       have hx : render (1:Grade R r)=(1:Truncated R) := by rw [show (1:Grade R r)=series R r (1:PTable R) from (map_one (series R r)).symm, series_render]; exact PowerSeries.trunc_one (R:=Marker.Poly R) r
       rw [value_render,hx,map_one];simp
    rw [spring,← valued (heat_seen ..) (Eventually.of_forall (heat_save R r F)) hi, _root_.funext ht]; exact h -- supply?
-- keep earn g factor explicitly . Expenses are true chart determinant constants not field scalar truncations.
lemma posts_vac (i:ℕ)(hi:i≤r): detail (logVac Ψ) R.quiet i + (if i=0 then Symmetry.price K F w x else 0) = (Adjacent.born ( Symmetry.Orbit.ground K F w W r ) C 0 r i x) + motion (fun t=> (earn F (G:=G) C t:ℂ)) i := by
    let d(t:ℝ):ℂ:= -(Symmetry.price K F w x)
    let k(t:ℝ):ℂ:= (earn F C (G:=G) t:ℂ)
    let z:=costPrice K F w C x
    have hu: logVac ξ= spring R r (fun t=> (bureau K F w C x t:ℂ)):=logWallet _ _ (pathT K F w C x) (origin0 K F w C x)
    have he: logVac Ψ= logVac ξ+ logVac Σ':= by
       rw [absolute_price K F w C W x r D hW B hB]; unfold logVac denominator;rw [map_mul]; have hp:= (accounts K F w W r).rolls C 0 r x; apply Cumulants.connected_mul
       · rw [bottom_quiet, stamped]; simp [entry,origin0]; -- may use Eq.Tx
       exact (bottom_quiet ..).trans hp
    rw [he, show detail (_+_) _ _=_ from (show detail (logVac ξ+ logVac Σ') R.quiet i=detail (logVac ξ) R.quiet i+detail (logVac Σ') R.quiet i from (by unfold detail;rw [observe_add,Marker.Poly.part_plus])),hu, spring_mark r (fun t=> (bureau K F w C x t:ℂ)) ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (pathT K F w C x))) i hi, ← flare K F w (d:=(0:V→ℤ)) W C r x i hi]
    have h₁:ContDiffAt ℝ ω k 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (fine_time (G:=G) F C)
    have h₂: ContDiffAt ℝ ω z 0:= (Symmetry.price_ready K F w).contDiffAt.comp (f:=unitx C x) _ (timeUnit C x)
    have h₃: ContDiffAt ℝ ω (fun t=>d t+z t) 0:= contDiffAt_const.add h₂
    rw [show (fun t:ℝ=> (bureau K F w C x t:ℂ))= fun t=> k t+(d t+z t) from ?_, madd h₁ h₃, madd contDiffAt_const h₂, mconst]; swap
    · funext t; simp [bureau,Symmetry.price,k,d,z,LocalScript.costPrice, unitx]; ring
    change motion k i + ((if i=0 then -_ else _) + motion z i)+_+_= (motion z i+_)+motion k i; split <;> abel
end YM.Comparison.RG02.FVAAlt2.Aperture
