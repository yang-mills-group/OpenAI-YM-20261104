import YM.LocalLTE.Fan.Cookie
/-! consumer component quantities. Carry β & mask U compressed. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)(p:Disk G c)
def barge (v:Finset (Veil c f))(X:Coat T F)(p:Disk G c)(n:ℕ)(R:Rep G f)(Q:YM.ConnectedActivityE6.Target G P)(a:ℝ)(b: Air f G):=∏ i∈ v, Bakers.afloat n (Fan.vows X R Q a p b i)
section
variable (H: Cash W t μ L Q o a T R)(he:X.x=t)(hX:X.width=o.K)(hp:(timeΛ X p).manifest)(D:Finset (Veil c f))(I:Finset (Tubular f G))
variable (hI : 1≤B)(r:ℕ→ℕ)(z:Veil c f→ℝ)(hT:∀ i∈D,0≤z i ∧ z i≤1∧ ∀ b:Air f G, |vows X R Q o.a p b i|≤z i*B^(levy r i))
include he hX hI hT H
local notation "A₀" => Fan.pool I X p
local notation "CA"=>cabinet I
local notation "Z"=> (∏ i∈ D,z i)
local notation "ℋ"=> (2+Real.exp 1)
include hp
lemma shipments (m:ℕ)(s:ℝ)(k:ℝ) (hk:(A₀).real (CA s)ᶜ ≤ k) : let g i:= barge D X p m R Q o.a (Pond.spill I i)
    |bars I (timeΛ X p) (arm D) R Q.table W o.a Q.halo - ∫ i in cabinet I s,g i ∂A₀| ≤ ℋ^D.card*Z*(k+D.card*(B^Pastel.mini)^m):=by
  intro g
  let f i:= node X p R Q o.a D (Pond.spill I i)
  have hb:0<B:=zero_lt_one.trans_le hI; let d:=D.card; have hr:0<(B:ℝ)^Pastel.mini:=Real.rpow_pos_of_pos hb _
  have hh₁:B^mini≤1:= Real.rpow_le_one_of_one_le_of_nonpos hI (by unfold mini; norm_num)
  have ht i (hi:i∈D)(b): |vows X R Q o.a p b i| ≤ z i*B^mini:= (hT i hi|>.2.2 b).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hI (financial _ _ _ _)) (hT i hi|>.1))
  let V:= ℋ^d*Z
  have hP (x:(Body (↥I))):= Bakers.rays (D:=D) (p:=fun i=> vows X R Q o.a p (Pond.spill I x) i) z (fun i hi=>(hT i hi).1) (fun i hi=>(hT i hi).2.1) (fun i hi=> ht i hi _) hr hh₁ m
  have hv (x:(Body (↥I))): ‖f x‖≤ V ∧ ‖g x‖≤V ∧ ‖f x-g x‖≤ V*(d*(B^mini)^m):= hP x
  have h₀:0 ≤ V:=(norm_nonneg _).trans ((hv 0).1)
  have heq:bars I (timeΛ X p) (arm D) R Q.table W o.a Q.halo= ∫ x,f x ∂A₀ := spool X _ _ I ((H.laws.data.localP F (timeΛ X p) (show (timeΛ X p).x=t from he) (show (timeΛ X p).width=o.K from hX) hp).sails.fullC.submatrix Subtype.val_injective) W
  rw [heq]
  let T:=CA s
  have hf₀ i:= (vow_b X H he hX i p).comp (Pond.spill_m I)
  have hF: Integrable f A₀:= (integrable_const V).mono' (show Measurable f from Finset.measurable_fun_prod _ fun i _=> (Real.measurable_exp.comp (hf₀ i)).sub measurable_const).aestronglyMeasurable (ae_of_all _ (fun i=> (hv i).1))
  have hQ: Integrable g A₀:= (integrable_const V).mono' (show Measurable g from Finset.measurable_fun_prod _ fun i _=>Finset.measurable_fun_sum _ fun j _=> measurable_const.mul ((hf₀ i).pow_const (j.val+1))).aestronglyMeasurable (ae_of_all _ (fun i=>(hv i).2.1)) -- edit
  have hs:= alive I s; rw [← integral_add_compl hs hF]
  let a:= ∫ i in T,f i ∂A₀; let b:= ∫ i in T,g i ∂A₀; let w:= ∫ i in Tᶜ,f i ∂A₀; let r:= (d:ℝ)*(B^mini)^m
  have he : a-b=∫ i in T, f i-g i ∂A₀ := Eq.symm (integral_sub hF.integrableOn hQ.integrableOn)
  have hy: |a-b| ≤ V*r:= by
    rw [he]
    let K:=V*r; have hp:0≤r:= by unfold r; positivity
    apply le_trans (MeasureTheory.norm_integral_le_integral_norm (μ:=(A₀).restrict T) (fun x=>f x-g x)); apply le_trans (b:=∫ _ in T,K ∂A₀)
    · exact MeasureTheory.integral_mono ((_root_.MeasureTheory.Integrable.norm (hF.sub hQ)).integrableOn) (integrable_const _) (fun x=> (hv x).2.2)
    rw [setIntegral_const]; exact mul_le_of_le_one_left (mul_nonneg h₀ hp) (measureReal_le_one)
  have hw: |w| ≤ V*k:= by
    apply (_root_.MeasureTheory.norm_integral_le_integral_norm (f:=f) ..).trans
    apply (MeasureTheory.setIntegral_mono (μ:=A₀) (s:=Tᶜ) (hF.norm).integrableOn (g:=fun _=>V) (integrable_const V) (fun x=> (hv x).1) -- edit
      ).trans
    rw [setIntegral_const,mul_comm]; exact mul_le_mul_of_nonneg_right hk h₀
  change |a+w-b|≤V*_ ; rw [show a+w-b=w+(a-b) by ring]; exact (abs_add_le ..).trans ((add_le_add hw hy).trans_eq (by rw [← mul_add]))
end
end YM.LocalLTE.Fan.Bakers
