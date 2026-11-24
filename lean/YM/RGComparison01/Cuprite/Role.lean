import YM.RGComparison01.Ward.Temper
import YM.RGComparison01.Pencils

/-!
# Root program for the new REAL model

 Warp result pushed through a cover loop. Doesn't assert vanishing at pose flat
 outside this particular stencil unless explicitly centred. Includes billing
 domain on the two radii and ALL WINDOW points. It's not necessary to find a
 model on the small Auxiliary with small global support threshold price (torons).
 Continuation uses only coupons after REAL reclosure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Cuprite
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup Pencils
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G:Gauge}{c L:Side}{j k n i:ℕ}{b v α p κ R r d a u:ℝ}
-- rating from ANY supplied e2 kernel.
section general
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def prom (k m:ℕ)(v a:ℝ):= (k+1:ℕ)*(|v|+(m+1:ℕ)*|a|)
lemma pledge (Y:AuxStage.Co E)(g:E→ℝ)(hg:Spline.Field i k Y)(x:E)(hp:AuxStage.Points v R⁻¹ b k j g x Y)(hr:0<R)(hR:R≤1)(he:‖x‖<R) (_hk : 2 ≤ k) (hxx : ∀ j≤2,∀ l≤ i, normJ l (headAt Y b j) 0*R^l≤ a*b^(2+1)) (hb:0<b)(hv:b≤1) : Brush j (prom k i v a*b^3) R⁻¹ (AuxStage.price Y b k) x :=by
   let C:=|v|+(i+1:ℕ)*|a|
   have hh n (hn:n∈Finset.range (k+1)) : Brush j (C*b^3) R⁻¹ (headAt Y b n) x:=by
      have hP:n≤k:=Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      by_cases hz:n≤2
      · let L:= b⁻¹ • ContinuousLinearMap.id ℝ E
        have hp:Spline i (headAt Y b n):= ((hg n hP).through L).smul (b^n)
        exact (Spline.all_taxes hp R he hR (hxx n hz)).climb (show ((i+1:ℕ):ℝ)*(a*b^3) ≤ C*b^3 from (by
          rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb.le _); exact (mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)).trans (le_add_of_nonneg_left (abs_nonneg _)))) le_rfl
      have hv': v ≤ C := (le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
      exact (hp.bill n hP).climb (mul_le_mul hv' (pow_le_pow_of_le_one hb.le hv (by omega)) (pow_nonneg hb.le _) (hp.nonneg.trans hv')) le_rfl
   have hz:= Brush.spree (Finset.range (k+1)) (headAt Y b) (fun _=> C*b^3) (inv_nonneg.mpr hr.le) hh; rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,←mul_assoc] at hz; exact hz
end general

variable (D : Ward.Duplex G n) (P:BudgetPoint)
local notation "Y"=> Positions (Uniform.Primary c G)

abbrev inhabit (D: Ward.Duplex G n)(x:Site c)(Z:AuxStage.Co (Positions (Uniform.Primary c G)))(b:ℝ)(k:ℕ):Config G c→ℝ:= D.C.chant x (AuxStage.price Z b k)
variable (o:Site c)(Z:AuxStage.Co (Positions (Uniform.Primary c G)))(F:Config G c→ℝ)
local notation "t₀"=> inhabit D o Z b k
lemma terrace (he : GaugeInvariant F) : GaugeInvariant (Boulevard.stillA F) := by intro i U; change F _ - _=F _- _; rw [he i U]
lemma sky (x:Positions (Uniform.Primary c G)) (he: Ward.awake x∈ Boulevard.sunny P) : ∀ᶠ y in 𝓝 x,Ward.awake y∈ Boulevard.sunny P:= by
   have h: Continuous (fun x:Positions (Uniform.Primary c G)=> Ward.awake x):=by
     exact continuous_pi (fun i=> ((show Continuous (fun x:Bid.Dir G c=> represent x i) from (by unfold represent increment Exterior.collect; simp only [Pi.one_apply,mul_one]; exact G.lieExp_cont.comp (continuous_apply _)))).comp (ContinuousLinearEquiv.continuous _))
   exact h.continuousAt.preimage_mem_nhds ((Boulevard.sky P).mem_nhds he)
lemma skies (x:Site c)(z:G.El)(V:Config G c)(h:V∈Boulevard.sunny P) : Ward.toral x z V ∈ Boulevard.sunny P:= by
   intro i; unfold Ward.toral; change G.chord (travel (gauge _ V) _ _)< _; simp_rw [travel_gauge,square_stop,G.chord_conj]; exact h i
variable (hp:Spline.Field i k Z)
variable (h:∀ x:Positions (Uniform.Primary c G), ‖x‖+u<R → Boulevard.actual x∈ Boulevard.sunny P → AuxStage.Points v R⁻¹ b k j (Boulevard.stillA F ∘ Boulevard.actual) x Z)
local notation "F₁"=> (Boulevard.stillA F)
local notation "S"=> (Boulevard.sunny P)
include hp
lemma proposal  : ContDiff ℝ (↑j:WithTop ℕ∞) (AuxStage.price Z b k):= by -- omit later
   unfold AuxStage.price; refine ContDiff.sum (fun p hp'=> ?_)
   let L:= b⁻¹ • ContinuousLinearMap.id ℝ (Positions (Uniform.Primary c G))
   exact (((hp p (Nat.le_of_lt_succ (Finset.mem_range.mp hp'))).through L).smul (b^p)).smooth _
variable (hv:D.Blurb c r R u) (hk : 1 ≤ n) (hr : r ≤ 1) (hr' : 0<r) (hj : j ≤ n)
omit hp
lemma centered (f:Config G c→ℝ)(x:Positions (Uniform.Primary c G))(hx:Brush j p d (f ∘ Boulevard.actual) x)(hP : Brush j p d (f ∘ Boulevard.actual) 0) : Brush j (2*p) d (Boulevard.stillA f ∘ Boulevard.actual) x := by
   have hp : ‖f 1‖≤ p:=by
     have h':=hP.bound; rw [Function.comp_apply,Pencils.created] at h'; exact h'
   exact (hx.separating ((Brush.certified (x:=x) hx.pos (f 1)).climb hp le_rfl)).climb (by linarith only) le_rfl
include hp h hv hk hr hr' hj
lemma modelled (X:Positions (Uniform.Primary c G))(hx : ‖X‖ < r)(hX : Boulevard.actual X∈ Boulevard.sunny P)(he : GaugeInvariant F): Brush j (2*D.conjCost j c*v*b^(k+1)) r⁻¹ (Boulevard.stillA (F-t₀) ∘ Boulevard.actual) X:= by
   have hh y (hy:‖y‖<r)(hY:Boulevard.actual y ∈ S) := Ward.Duplex.sways (Boulevard.stillA F) (AuxStage.price Z b k) D o hv (fun i U h=>⟨skies P o i U h, terrace F he _ _⟩) (proposal Z hp) (fun y hy hV=>(h y hy hV).tail) hk hr hr' hj (sky P) y hy hY
   let H:= F₁-t₀
   have hw: Boulevard.stillA H=Boulevard.stillA (F-t₀):=by ext x; simp only [Boulevard.stillA,H,Pi.sub_apply]; abel
   rw [← hw]; rw [mul_assoc 2,mul_assoc 2, mul_assoc (D.conjCost j c)] -- maybe
   exact centered H X (hh X hx hX) (hh 0 (by simpa) (by rw [Pencils.created]; exact Pencils.blue P))

lemma model_cost (X:Positions (Uniform.Primary c G))(hx:‖X‖<r)(hX:Boulevard.actual X∈ S)
    (hR:R≤1)(hp':0≤u)(he:∀ j≤2,∀ l ≤ i,normJ l (headAt Z b j) 0 * R^l ≤ a*b^(2+1))(hb:0<b)(ht:b≤1)(hK:2 ≤ k): Brush j (2*D.conjCost j c*prom k i v a*b^3) r⁻¹ (Boulevard.stillA t₀ ∘ Boulevard.actual) X:=by
   let f (_:Config G c):=(0:ℝ)
   let S':= Boulevard.sunny P («G»:=G) («c»:=c)
   have h' (y:Positions (Uniform.Primary c G))(hy:‖y‖<r)(hY:Boulevard.actual y ∈ S') : Brush j (D.conjCost j c * (prom k i v a*b^3)) r⁻¹ (t₀ ∘ Boulevard.actual) y := by
      have H : Brush j (D.conjCost j c * (prom k i v a*b^3)) _ ((f-t₀)∘Boulevard.actual) y:= Ward.Duplex.sways («S»:=S') f (AuxStage.price Z b k) D o hv (fun i U h=>⟨skies P o i U h,rfl⟩) (proposal Z hp) (fun y hy he' => ?_) hk hr hr' hj (sky P) y hy hY
      swap
      · have ht:=(pledge Z _ hp y (h _ hy he') (hr'.trans_le hv.rootF) hR ((le_add_of_nonneg_right hp').trans_lt hy) hK he hb ht).opposite
        exact ht.shimmy (Eventually.of_forall fun i=> by simp [f])
      exact H.opposite.shimmy (Eventually.of_forall fun v=> by simp [f])
   rw [mul_assoc 2,mul_assoc 2, mul_assoc (D.conjCost j c)]; exact centered _ _ (h' X hx hX) (h' 0 (by simpa) (by rw [Pencils.created]; exact Pencils.blue P))
end YM.RGComparison01.Cuprite
