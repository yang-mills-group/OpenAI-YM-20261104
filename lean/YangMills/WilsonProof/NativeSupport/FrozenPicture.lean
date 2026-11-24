import YM.RGComparison.Core16.HistoryIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Function Filter Finset MeasureTheory Lattice RG Wilson RGComparison.Core16
open YM.Push.BetaTransport YM.Pressure Tree Real
open scoped Classical Topology BigOperators
namespace WilsonUniformUnmarkedInletSignedResponse
private theorem pulse {X:Type*}[MeasurableSpace X](μ:Measure X)[IsFiniteMeasure μ]
    {f s:X→ℝ}(hf:Envelope f)(hs:Envelope s):
    HasDerivAt (fun z:ℝ=>∫ x,exp ((-z)*s x)*f x ∂μ) (∫ x,(-s x)*f x ∂μ) 0:=by
  obtain ⟨A,wa⟩:=hf.cost
  obtain ⟨B,wb⟩:=hs.cost
  let F (z:ℝ)(x:X):=exp ((-z)*s x)*f x
  let v (z:ℝ)(x:X):=(-s x)*F z x
  have test (z:ℝ):Envelope (F z):=((Envelope.const (-z)).mul hs).exp.mul hf
  have bound:∀ᵐ x ∂μ,∀z∈Set.Ioo (-1:ℝ) 1, ‖v z x‖ ≤ |B| * (exp |B| * |A|):=by
    refine ae_of_all μ fun x z hz=>?_
    have scan:|z| ≤ 1:=abs_le.mpr ⟨hz.1.le,hz.2.le⟩
    have en:|s x| ≤ |B|:=(wb x).trans (le_abs_self _)
    have src:‖f x‖ ≤ |A|:=(wa x).trans (le_abs_self _)
    have warm:(-z)*s x ≤ |B|:=calc
      _ ≤ |(-z)*s x|:=le_abs_self _
      _ = |z| * |s x|:=by rw [abs_mul,abs_neg]
      _ ≤ 1*|B|:=mul_le_mul scan en (abs_nonneg _) (by norm_num)
      _ = _:=one_mul _
    simp only [v,F,norm_mul,norm_neg,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul en (mul_le_mul (exp_le_exp.mpr warm) src (norm_nonneg _) (exp_pos _).le)
      (mul_nonneg (exp_pos _).le (norm_nonneg _)) (abs_nonneg _)
  have slope:∀ᵐ x ∂μ,∀z∈Set.Ioo (-1:ℝ) 1, HasDerivAt (fun y=>F y x) (v z x) z:=by
    refine ae_of_all μ fun x z _=>?_
    have rate:=(((hasDerivAt_id z).neg.mul_const (s x)).exp.mul_const (f x))
    convert rate using 1 <;> first | rfl | (dsimp [F,v];ring)
  have diff:=(hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ)
    (F:=F) (F':=v) (bound:=fun _=>|B| * (exp |B| * |A|))
    (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
    (Eventually.of_forall fun z=>(test z).meas.aestronglyMeasurable) ((test 0).integrable μ)
    ((hs.neg.mul (test 0)).meas.aestronglyMeasurable) bound (integrable_const _) slope).2
  simpa only [v,F,neg_zero,zero_mul,exp_zero,one_mul] using diff

variable {G:Gauge}{n c:Side}(d:Descent n c)
def line (β v:ℕ→ℝ)(z:ℝ)(i:ℕ):=β i+z*v i

theorem account (β v:ℕ→ℝ)(z:ℝ)(t:d.Tags)(V:Config G c)(x:Descent.Fields G d):
    d.account (line β v z) t V x = d.account β t V x+z*d.account v t V x:=by
  induction d generalizing β v with
  | nil=>change (β 0+z*v 0)*energy V=β 0*energy V+z*(v 0*energy V);ring
  | @push m i S T d ih=>
    simp only [Descent.account]
    rw [show Descent.upβ (line β v z)=line (Descent.upβ β) (Descent.upβ v) z from rfl,ih]
    unfold line
    ring

private theorem atField {X:Type*}[MeasurableSpace X]{p:Config G c × X→ℝ}
    (bill:Envelope p)(V:Config G c):Envelope (fun x=>p (V,x)):=by
  refine ⟨bill.meas.comp (measurable_const.prodMk measurable_id),?_⟩
  obtain ⟨C,h⟩:=bill.cost
  exact ⟨C,fun x=>h (V,x)⟩

theorem tag (h:d.OK G)(β v:ℕ→ℝ)(t:d.Tags)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ):
    HasDerivAt (fun z=>∫ x,d.integrand (line β v z) t φ V x ∂d.measure G)
      (∫ x,(-d.account v t V x)*d.integrand β t φ V x ∂d.measure G) 0:=by
  have paid:=pulse (d.measure G) (atField (d.path_envelope h β t φ neat) V) (atField (d.account_envelope h v t) V)
  convert paid using 1
  funext z
  apply integral_congr_ae
  refine ae_of_all _ fun x=>?_
  change d.integrand (line β v z) t φ V x=exp ((-z)*d.account v t V x)*d.integrand β t φ V x
  simp only [Descent.integrand,account]
  rw [show -(d.account β t V x+z*d.account v t V x)=(-z)*d.account v t V x+(-d.account β t V x) by ring,exp_add]
  ring

theorem measured (h:d.OK G)(β v:ℕ→ℝ)(t:d.Tags)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ):
    Integrable (fun x=>(-d.account v t V x)*d.integrand β t φ V x) (d.measure G):=
  ((atField (d.account_envelope h v t) V).neg.mul (atField (d.path_envelope h β t φ neat) V)).integrable _


end WilsonUniformUnmarkedInletSignedResponse
namespace WilsonUniformUnmarkedInletConnectedCovariance
variable {G : Gauge} {n c : Side} (d : Descent n c)
def mass (β:ℕ→ℝ)(φ:Config G n→ℝ)(V:Config G c):=
  ∑ t,∫ x,d.integrand β t φ V x ∂d.measure G

def insertion (β v:ℕ→ℝ)(φ:Config G n→ℝ)(V:Config G c):=
  ∑ t,∫ x,(-d.account v t V x)*d.integrand β t φ V x ∂d.measure G

private theorem vacuum (h:d.OK G)(β:ℕ→ℝ)(V:Config G c):
    d.vacuum β V=d.scalar G β*mass d β (1:Config G n→ℝ) V:=by
  rw [←Descent.weighted_unit]
  exact d.path_formula h β continuous_const (fun _ _=>rfl) V

theorem positive (h:d.OK G)(β:ℕ→ℝ)(V:Config G c):0 < mass d β (1:Config G n→ℝ) V:=by
  apply (mul_pos_iff_of_pos_left (Descent.scalar_pos G d β)).mp
  rw [←vacuum d h β V]
  exact d.positive β h V

theorem fraction (h:d.OK G)(β:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ)(symm:GaugeInvariant φ):
    d.conditioned β φ V=mass d β φ V/mass d β 1 V:=by
  have cost:d.weighted β φ V=d.scalar G β*mass d β φ V:=d.path_formula h β neat symm V
  rw [Descent.conditioned,smul_eq_mul,cost,vacuum d h β V]
  field_simp [(Descent.scalar_pos G d β).ne',(positive d h β V).ne']

private theorem summed (h:d.OK G)(β v:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ):
    HasDerivAt (fun r=>mass d (WilsonUniformUnmarkedInletSignedResponse.line β v r) φ V) (insertion d β v φ V) 0:=by
  apply HasDerivAt.fun_sum
  exact fun t _=>WilsonUniformUnmarkedInletSignedResponse.tag d h β v t V neat

theorem centered (h:d.OK G)(β v:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ)(a:ℝ):
    insertion d β v (fun U=>φ U-a) V=insertion d β v φ V-a*insertion d β v 1 V:=by
  unfold insertion
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _=>?_
  have pay:=WilsonUniformUnmarkedInletSignedResponse.measured d h β v t V neat
  have unit:=WilsonUniformUnmarkedInletSignedResponse.measured d h β v t V (φ:=1) continuous_const
  rw [←integral_const_mul,←integral_sub pay (unit.const_mul a)]
  apply integral_congr_ae
  refine ae_of_all _ fun x=>?_
  simp only [Descent.integrand,Pi.one_apply]
  ring

theorem connected (h:d.OK G)(β v:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ)(symm:GaugeInvariant φ):
    HasDerivAt (fun r=>d.conditioned (WilsonUniformUnmarkedInletSignedResponse.line β v r) φ V)
      (insertion d β v (fun U=>φ U-d.conditioned β φ V) V/mass d β 1 V) 0:=by
  have start:WilsonUniformUnmarkedInletSignedResponse.line β v 0=β:=by funext i;simp [WilsonUniformUnmarkedInletSignedResponse.line]
  have den:mass d (WilsonUniformUnmarkedInletSignedResponse.line β v 0) (1:Config G n→ℝ) V≠0:=by rw [start];exact (positive d h β V).ne'
  have tangent:=(summed d h β v V neat).div (summed d h β v V (φ:=1) continuous_const) den
  rw [start] at tangent
  rw [show (fun r=>d.conditioned (WilsonUniformUnmarkedInletSignedResponse.line β v r) φ V)=
      (fun r=>mass d (WilsonUniformUnmarkedInletSignedResponse.line β v r) φ V/mass d (WilsonUniformUnmarkedInletSignedResponse.line β v r) 1 V)
      from funext fun r=>fraction d h _ V neat symm]
  apply tangent.congr_deriv
  rw [centered d h β v V neat,fraction d h β V neat symm]
  field_simp [(positive d h β V).ne']


end WilsonUniformUnmarkedInletConnectedCovariance
open WilsonUniformUnmarkedInletConnectedCovariance
namespace WilsonUniformUnmarkedInletConnectedShift
variable {G : Gauge} {n c : Side} (d : Descent n c)
abbrev temperatures:=WilsonUniformUnmarkedInletSignedResponse.line

def responseAt (β v:ℕ→ℝ)(V:Config G c)(φ:Config G n→ℝ)(r:ℝ):=
  let Y:=temperatures β v r
  insertion d Y v (fun x=>φ x-d.conditioned Y φ V) V/mass d Y 1 V

theorem derivative (h:d.OK G)(β v:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ)(symm:GaugeInvariant φ)(r:ℝ):
    HasDerivAt (fun z=>d.conditioned (temperatures β v z) φ V) (responseAt d β v V φ r) r:=by
  let Y:=temperatures β v r
  have base:HasDerivAt (fun z=>d.conditioned (temperatures Y v z) φ V) (responseAt d β v V φ r) (r-r):=by
    rw [sub_self]
    exact connected d h Y v V neat symm
  have inner:HasDerivAt (fun z:ℝ=>z-r) 1 r:=(hasDerivAt_id r).sub_const r
  have translated:HasDerivAt (fun z=>d.conditioned (temperatures Y v (z-r)) φ V) (responseAt d β v V φ r) r:=by
    simpa only [Function.comp_def,mul_one] using base.comp (h:=fun z:ℝ=>z-r) r inner
  have same:(fun z=>d.conditioned (temperatures Y v (z-r)) φ V)=(fun z=>d.conditioned (temperatures β v z) φ V):=by
    funext z
    congr 1
    funext i
    change β i+r*v i+(z-r)*v i=β i+z*v i
    ring
  rw [same] at translated
  exact translated

theorem shift (h:d.OK G)(β v:ℕ→ℝ)(V:Config G c){φ:Config G n→ℝ}(neat:Continuous φ)(symm:GaugeInvariant φ):
    ∃r∈Set.Ioo (0:ℝ) 1,d.conditioned (β+v) φ V-d.conditioned β φ V=responseAt d β v V φ r:=by
  let F:=fun z:ℝ=>d.conditioned (temperatures β v z) φ V
  have deriv (r:ℝ):HasDerivAt F (responseAt d β v V φ r) r:=derivative d h β v V neat symm r
  have cont:Continuous F:=continuous_iff_continuousAt.mpr fun r=>(deriv r).continuousAt
  obtain ⟨r,inside,eq⟩:=exists_hasDerivAt_eq_slope F (responseAt d β v V φ) (by norm_num : (0:ℝ)<1)
    cont.continuousOn (fun r _=>deriv r)
  have zero:temperatures β v 0=β:=by funext i;simp [temperatures,WilsonUniformUnmarkedInletSignedResponse.line]
  have one:temperatures β v 1=β+v:=by funext i;simp [temperatures,WilsonUniformUnmarkedInletSignedResponse.line]
  refine ⟨r,inside,?_⟩
  simpa only [F,zero,one,sub_zero,div_one] using eq.symm


end WilsonUniformUnmarkedInletConnectedShift
namespace WilsonUniformUnmarkedInletEnergySites
def sites (n:Side):{c:Side} → Descent n c → Type
  | _,.nil=>Face (Per n)
  | c,.push _ _ d=>Bond c ⊕ sites n d

instance siteType {n c:Side}(d:Descent n c):Fintype (sites n d):=by
  induction d with
  | nil=>change Fintype (Face (Per n));infer_instance
  | @push m i S T d ih=>change Fintype (Bond m ⊕ sites n d);letI:=ih;infer_instance

def lag {n:Side}:{c:Side} → (d:Descent n c) → sites n d → ℕ
  | _,.nil=>fun _=>0
  | _,.push _ _ d=>Sum.elim (fun _=>1) (fun j=>lag d j+1)

def cell (G:Gauge){n:Side}:{c:Side} → (d:Descent n c) → d.Tags → Config G c → Descent.Fields G d → sites n d → ℝ
  | _,.nil,_,V,_=>fun a=>G.price (faceValue V a)
  | _,.push S T d,t,V,x=>Sum.elim (fun b=>linkEnergy S (V b*(S.prediction (T.drape (x ∘ Sum.inl)) t.1 b)⁻¹))
      (cell G d t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr))

def cap {n:Side}:{c:Side} → (d:Descent n c) → sites n d → ℝ
  | _,.nil=>fun _=>2
  | _,.push S _ d=>Sum.elim (fun _=>linkCap S) (cap d)

variable {G:Gauge}{n c:Side}
theorem bounded (d:Descent n c)(t:d.Tags)(V:Config G c)(x:Descent.Fields G d)(q:sites n d):
    0 ≤ cell G d t V x q ∧ cell G d t V x q ≤ cap d q:=by
  induction d with
  | nil=>exact G.price_range _
  | @push m i S T d ih=>
    rcases q with b|b
    · exact ⟨(link_estimate S).nonneg _,(link_estimate S).bound _⟩
    · exact ih .. 

theorem dates (d:Descent n c)(q:sites n d):lag d q ≤ d.depth ∧ (0 < d.depth  →  0 < lag d q):=by
  induction d with
  | nil=>change 0 ≤ 0 ∧ (0 < 0 → 0 < 0);exact ⟨le_rfl,id⟩
  | @push m i S T d ih=>
    rcases q with b|b
    · change 1 ≤ d.depth+1 ∧ _;exact ⟨by omega,fun _=>Nat.zero_lt_succ _⟩
    · change lag d b+1 ≤ d.depth+1 ∧ _;exact ⟨Nat.succ_le_succ (ih b).1,fun _=>Nat.zero_lt_succ _⟩

theorem expanded (d:Descent n c)(v:ℕ → ℝ)(t:d.Tags)(V:Config G c)(x:Descent.Fields G d):
    d.account v t V x=∑a:sites n d,v (lag d a)*cell G d t V x a:=by
  induction d generalizing v with
  | nil=>change v 0*(∑q:Face (Per n),G.price (faceValue V q))=∑q:Face (Per n),v 0*G.price (faceValue V q);rw [Finset.mul_sum]
  | @push m i S T d ih=>
    change v 1*tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V+d.account (Descent.upβ v) t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr)=
      ∑q:Bond m ⊕ sites n d,v (lag (Descent.push S T d) q)*cell G (Descent.push S T d) t V x q
    rw [Fintype.sum_sum_type,ih]
    congr 1
    change v 1*(∑b:Bond m,linkEnergy S (V b*(S.prediction (T.drape (x ∘ Sum.inl)) t.1 b)⁻¹))=
      ∑b:Bond m,v 1*linkEnergy S (V b*(S.prediction (T.drape (x ∘ Sum.inl)) t.1 b)⁻¹)
    rw [Finset.mul_sum]

def interior (d:Descent n c):Finset (sites n d):=univ.filter fun q=>0 < lag d q ∧ lag d q < d.depth

theorem middle (d:Descent n c)(v:ℕ → ℝ)(endValue:v d.depth=0)(t:d.Tags)(V:Config G c)(x:Descent.Fields G d):
    d.account v t V x=∑a∈interior d,v (lag d a)*cell G d t V x a:=by
  rw [expanded]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro q _ gone
  have missing:¬(0 < lag d q ∧ lag d q < d.depth):=by simpa only [interior,Finset.mem_filter,Finset.mem_univ,true_and] using gone
  have served:=dates d q
  have dead:lag d q=d.depth:=by by_cases b:0 < d.depth <;> omega
  rw [dead,endValue,zero_mul]


end WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletEnergySites
namespace WilsonUniformUnmarkedInletBondCovariances
variable {G : Gauge} {n c : Side}
private theorem measurableCell (d:Descent n c)(h:d.OK G)(t:d.Tags)(q:sites n d):
    Measurable (fun z:Config G c × Descent.Fields G d=>cell G d t z.1 z.2 q):=by
  induction d with
  | nil=>
    change Measurable fun z:Config G n × Descent.Fields G Descent.nil=>G.price (faceValue z.1 q)
    apply Continuous.measurable
    unfold faceValue
    fun_prop
  | @push m i S T d ih=>
    let D:=Descent.push S T d
    have held:Measurable (fun z:Config G m × Descent.Fields G D=>T.drape (z.2 ∘ Sum.inl)):=
      T.continuous_drape.measurable.comp ((measurable_pi_lambda _ fun _=>measurable_pi_apply _).comp measurable_snd)
    have rest:Measurable (fun z:Config G m × Descent.Fields G D=>z.2 ∘ Sum.inr (α:=T.Free)):=
      (measurable_pi_lambda _ fun _=>measurable_pi_apply _).comp measurable_snd
    rcases q with b|b
    · have signal:Measurable fun z:Config G m × Descent.Fields G D=>S.prediction (T.drape (z.2 ∘ Sum.inl)) t.1 b:=
        (measurable_pi_apply b).comp ((S.prediction_meas h.1 t.1).comp held)
      have coarse:Measurable fun z:Config G m × Descent.Fields G D=>z.1 b:=(measurable_pi_apply b).comp measurable_fst
      exact measurable_const.mul (G.continuous_price.measurable.comp (coarse.mul signal.inv))
    · exact (ih h.2 t.2 b).comp (held.prodMk rest)

private theorem integrableCell (d:Descent n c)(h:d.OK G)(β:ℕ → ℝ)(t:d.Tags)(V:Config G c){φ:Config G n → ℝ}
    (test:Continuous φ)(q:sites n d):
    Integrable (fun x=>(-cell G d t V x q)*d.integrand β t φ V x) (d.measure G):=by
  have row:Envelope (fun z:Config G c × Descent.Fields G d=>cell G d t z.1 z.2 q):=by
    refine ⟨measurableCell d h t q,cap d q,?_⟩
    intro z
    have limits:=bounded d t z.1 z.2 q
    simpa only [Real.norm_of_nonneg limits.1] using limits.2
  have pair:=row.neg.mul (d.path_envelope h β t φ test)
  have slice:Envelope (fun x=>(-cell G d t V x q)*d.integrand β t φ V x):=by
    refine ⟨pair.meas.comp (measurable_const.prodMk measurable_id),?_⟩
    obtain ⟨C,hh⟩:=pair.cost
    exact ⟨C,fun x=>hh (V,x)⟩
  exact slice.integrable _

def entry (d:Descent n c)(β:ℕ → ℝ)(φ:Config G n → ℝ)(V:Config G c)(q:sites n d):=
  ∑ t,∫ x,(-cell G d t V x q)*d.integrand β t φ V x ∂d.measure G

theorem split (d:Descent n c)(h:d.OK G)(β v:ℕ → ℝ)(endValue:v d.depth=0)(V:Config G c)
    {φ:Config G n → ℝ}(test:Continuous φ):
    insertion d β v φ V=∑q∈interior d,v (lag d q)*entry d β φ V q:=by
  have perTag (t:d.Tags):(∫x,(-d.account v t V x)*d.integrand β t φ V x ∂d.measure G)=
      ∑q∈interior d,v (lag d q)*(∫x,(-cell G d t V x q)*d.integrand β t φ V x ∂d.measure G):=by
    calc
      _=∫x,∑q∈interior d,v (lag d q)*((-cell G d t V x q)*d.integrand β t φ V x) ∂d.measure G:=by
        apply integral_congr_ae
        refine ae_of_all _ fun x=>?_
        change (-d.account v t V x)*d.integrand β t φ V x=∑q∈interior d,v (lag d q)*((-cell G d t V x q)*d.integrand β t φ V x)
        rw [middle d v endValue,neg_mul,Finset.sum_mul,←Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun q _=>by ring
      _=∑q∈interior d,∫x,v (lag d q)*((-cell G d t V x q)*d.integrand β t φ V x) ∂d.measure G:=by
        apply integral_finsetSum
        exact fun q _=>(integrableCell d h β t V test q).const_mul _
      _=_:=Finset.sum_congr rfl fun _ _=>integral_const_mul _ _
  unfold insertion entry
  simp_rw [perTag]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _=>(Finset.mul_sum ..).symm

theorem centered (d:Descent n c)(h:d.OK G)(β v:ℕ → ℝ)(endValue:v d.depth=0)(V:Config G c)
    {φ:Config G n → ℝ}(test:Continuous φ)(r:ℝ):
    let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
    let F:=fun U=>φ U-d.conditioned Y φ V
    WilsonUniformUnmarkedInletConnectedShift.responseAt d β v V φ r=
      ∑q∈interior d,v (lag d q)*(entry d Y F V q/mass d Y 1 V):=by
  intro Y F
  change insertion d Y v F V/mass d Y 1 V=_
  have neat:Continuous F:=test.sub continuous_const
  rw [split d h Y v endValue V neat,Finset.sum_div]
  exact Finset.sum_congr rfl fun q _=>by ring


end WilsonUniformUnmarkedInletBondCovariances
open WilsonUniformUnmarkedInletConnectedCovariance WilsonUniformUnmarkedInletBondCovariances
namespace WilsonUniformUnmarkedInletBondRemainder
variable {G : Gauge} {n c : Side}
def picture (d:Descent n c)(β v:ℕ → ℝ)(V:Config G c)(φ:Config G n → ℝ)(r:ℝ)(q:sites n d):=
  let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
  entry d Y (fun U=>φ U-d.conditioned Y φ V) V q/mass d Y 1 V


end WilsonUniformUnmarkedInletBondRemainder
end YM.Integration
