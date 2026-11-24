import YM.LocalTaylorR2.Exponent.Vesta
/-! ## Adaptation of E6.Afresh.winglet. Post-period *only*.
 Give up exact quantitative rates, prove also integrable after multiplying by
 arbitrary *finite* powers of oscillators on the same projection used here.
 This allows uncut integral hypothesis for perturbation in each projected label. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {ι α E : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {L : Side} {A : Matrix ι ι ℝ} {t η b τ y : ℝ} {a v : Body ι}

omit [DecidableEq ι] in
private lemma dot_shapeS (v:Body ι) : dotProduct v.ofLp v.ofLp=‖v‖^2 := by simp_rw [dotProduct,EuclideanSpace.real_norm_sq_eq]; simp only [pow_two]

omit [DecidableEq ι] in
private lemma scalar_jetS (A : E→Matrix ι ι ℝ) (p : ∀ i j', Brush j b 1 (fun x=> A x i j') x)
    (_hf : 0≤b) (f : E→Body ι) (h : Brush j η 1 f x) :
    let v:= Fintype.card ι; let Q:ℝ:=↑v* (η*(↑v*(b*η)))
    Brush j (Q*(1+(1+(1+1)))^j) 1 (fun p=> dotProduct (WithLp.ofLp (f p)) (A p*ᵥ WithLp.ofLp (f p))) x := by
  intro v W
  have he i: Brush j η 1 (fun x=>f x i) x := by
    -- color general FIN
    let P:=EuclideanSpace.proj (𝕜:=ℝ) (ι:=ι) i
    have hp: ‖P‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      change ‖x i‖≤_; rw [one_mul,← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul]))
    have hv:= h.report P hp; rw [one_mul] at hv; exact hv
  have hx i := (((Brush.spree univ (fun j p=> A p i j*f p j) _ (show (0:ℝ) ≤ 1+1 by norm_num) (fun j (_:j∈univ)=>
      (p i j).paints (he j)))))
  simp only [sum_const,nsmul_eq_mul,card_univ] at hx
  have hh:= Brush.spree (univ (α:=ι)) _ _ (by norm_num) (fun j _=> (he j).paints (hx j)); simp only [sum_const,nsmul_eq_mul,card_univ] at hh
  exact hh.trim

lemma wingletR2 (k :ℕ) {A:E→Matrix ι ι ℝ} {Z:α → Body ι} {V:α→ E→ Body ι} (hp : (A x).PosDef)
    (h : Bottom (A x)⁻¹ t) (ht : 0<t) (hA : ∀ i j', ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun x=> A x i j') x) (hV : Zest
      (fun a x=> V a x-Z a) x j) :
    ∃ (M : Body ι→ℝ), Measurable M ∧ (∀ x,0≤M x) ∧ Integrable (fun x=> M x*(1+‖x‖)^k) (sweep (A x)) ∧ ∀ᶠ y in 𝓝 x,
      ∀ a, Brush j (M (Z a)) 1 (fun y=> lens₀ (A y) (V a y)/lens₀ (A x) (Z a)) y := by
  have hx:= isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  have he i k:= jetBack hA hx i k
  let P i:= (A i)⁻¹; let S := sweep (A x)
  obtain ⟨B,hB,hF⟩:=hV.post
  let s := Fintype.card ι; let v y:= -Real.log (A y).det/2
  obtain ⟨A',hA',hH⟩:= Brush.neighborhood x (((determinant hA).log hx.ne_zero).neg.div_const 2 : ContDiffAt ℝ (↑j) v x)
  choose m hk hQ using fun i j=> Brush.neighborhood x (he i j)
  let U := ∑ i:ι, ∑ j:ι,m i j; have htU : 0≤U := sum_nonneg fun _ _=> sum_nonneg fun j _=> (hk _ j).le
  have hm := (squarePulse (x:=x) P t ht h (fun i j=> (he i j).continuousAt))
  let f a y:= dotProduct (V a y).ofLp ((P y)*ᵥ(V a y).ofLp)
  let g a y:= v y - f a y/2
  have hh (p:ℝ) (x:E) (i:α) (hp:Brush j p 1 (fun x=> V i x) x) (h : ∀ i j, Brush _ U 1 (fun x=>P x i j) x) :=
    scalar_jetS P h htU (V i) hp
  obtain ⟨C,hC,hΨ⟩:= Brush.neighborhood (k:=j) 0 Real.contDiff_exp.contDiffAt
  let n y := A'+((s:ℝ)*(y*(s*(U*y))))*(1+(1+(1+1)))^j
  let b y := (1+(1+(j.factorial:ℝ)*C)*(1+(n y+n y)))^j
  let X : ℝ := t/8; let D:=(t/4)*B^2
  let Z':= ((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹
  have hz:0≤Z':= by unfold Z'; positivity
  let F (z:Body ι):= Z' * Real.exp (A'+D-X * ‖z‖^2)* b (B+ ‖z‖)/lens₀ (A x) z
  have hF' : Measurable F := by
    unfold F; refine Measurable.div (show Measurable _ from ?_) (bulbB (fun _ _=> measurable_const : Art.Borel (fun _ : Body ι=> A x)) measurable_id)
    unfold b n; fun_prop
  have hb :∀ t:ℝ,0≤t→0≤b (B+t) := by intro t ht; unfold b n; positivity
  have hnn (z:Body ι):0≤F z:=by unfold F; exact div_nonneg (mul_nonneg (mul_nonneg hz (Real.exp_pos _).le) (hb _ (norm_nonneg _))) (fullFuel _ _).le
  refine ⟨F,hF',hnn,?_,?_⟩
  swap
  · filter_upwards [hm,hF,hH,eventually_all.mpr (fun i=> eventually_all.mpr (hQ i))] with y hp hv hh' hz' a
    have hp' : Brush j (B+‖Z a‖) 1 (V a) y := ((hv a).gathering (Brush.certified zero_le_one (Z a))).shimmy
      (Eventually.of_forall fun _=> (sub_add_cancel ..).symm)
    have hx: Brush j (n (B+‖Z a‖)) 1 (g a) y := hh'.separating (semi (hh _ _ _ hp' (fun i j=>
      (hz' i j).climb ((Finset.single_le_sum (fun b _=>(hk _ b).le) (mem_univ j)).trans (Finset.single_le_sum
      (f:=fun i=> ∑ j,m i j) (fun i _=>sum_nonneg fun j _=> (hk _ _).le) (mem_univ i))) le_rfl)))
    have hSS y : lens₀ (A y) (V a y)= Z'*Real.exp (g a y) := rfl
    have hz' := ((Blaze.fever _ (hx.separating ((Brush.certified zero_le_one _).climb hx.bound le_rfl)) hΨ.self_of_nhds).trim.smul Z').smul (lens₀ (A x) (Z a))⁻¹
    have hP:= fullFuel (A x) (Z a)
    apply (hz'.climb ?_ le_rfl).shimmy (Eventually.of_forall (fun t=> by
      change lens₀ _ _ / _= (lens₀ (A x) (Z a))⁻¹ * (Z' * _); rw [hSS]; ring))
    unfold F; rw [Real.norm_of_nonneg hz, norm_inv, Real.norm_of_nonneg hP.le]
    have hv': f a y≥ t/2 * ‖V a y‖^2 := (mul_le_mul_of_nonneg_left (dot_shapeS _).symm.le (by positivity)).trans (hp _)
    have hs: ‖Z a‖^2 ≤ 2*(‖V a y‖^2+B^2) := by
      have he := (hv a).bound; have hh : ‖Z a‖ ≤ ‖V a y‖+B := by
        nth_rw 1 [show Z a=V a y-(V a y-Z a) from by abel]; exact (norm_sub_le ..).trans (add_le_add_right he _)
      nlinarith [norm_nonneg (Z a),norm_nonneg (V a y),sq_nonneg (‖V a y‖-B)]
    have hf' : g a y ≤ A'+D-X*‖Z a‖^2 := by unfold g D X; nlinarith only [hv', show v y≤A' from (le_abs_self _).trans hh'.bound, mul_le_mul_of_nonneg_left hs ht.le]
    change _⁻¹*(Z'*(Real.exp (g a y)*b _))≤_
    rw [div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hP.le)
    rw [mul_assoc Z' (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ hz
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hf'); unfold b; have hf:=hx.nonneg; positivity
  -- polynomial absorbed into exponential, rank and κ entirely free here
  let N := n (B+1); let P:= 1+(1+(j.factorial:ℝ)*C)*(1+(N+N)); let y:= X/2
  let D' := (2*(j:ℝ)+(k:ℝ))^2/(4*y)
  let H := Z'*P^j*Real.exp (A'+D+D')
  have hs: 0≤(s:ℝ):= Nat.cast_nonneg _
  have hN :0≤N := by unfold N n; positivity
  have h' :0<y := by unfold y X; positivity
  have hP: 0<P := by unfold P; positivity
  apply ((Flux.protect hp h').const_mul H).mono' (hF'.mul (show Measurable (fun z:Body ι=> (1+‖z‖)^k) by fun_prop)).aestronglyMeasurable
  apply ae_of_all; intro z
  have hP' := (fullFuel (A x) z).le
  have hp :0≤ F z := by unfold F; exact div_nonneg (mul_nonneg (mul_nonneg hz (Real.exp_pos _).le) (hb _ (norm_nonneg _))) hP'
  rw [Pi.mul_apply,Real.norm_of_nonneg (mul_nonneg hp (by positivity))]; unfold F
  let t:= ‖z‖; let U' := (1+t); have ht:0≤t := norm_nonneg _; have hu: 1≤U' := le_add_of_nonneg_right ht
  have hF : b (B+t)≤ P^j*Real.exp (2*j*t) := by
    have hf := Real.add_one_le_exp t; rw [add_comm] at hf
    have hh : B+t ≤ (B+1)*U' := by unfold U'; nlinarith only [hB,ht]
    have hp:n (B+t)≤N*U'^2 := by
      have hbb : n (B+t) ≤ n ((B+1)*U') := by unfold n; gcongr
      apply hbb.trans; unfold N n; rw [add_mul A']
      apply add_le_add (le_mul_of_one_le_right hA'.le (one_le_pow₀ hu)); exact le_of_eq (by ring)
    have hx' : 1+(1+(j.factorial:ℝ)*C)*(1+(n (B+t)+n (B+t))) ≤ P*U'^2 := by
      unfold P; nlinarith only [one_le_pow₀ (n:=2) hu,hp,mul_le_mul_of_nonneg_left hp (show 0≤(j.factorial:ℝ)*C by positivity), show 0≤(j.factorial:ℝ)*C by positivity]
    unfold b; apply le_trans (b:=(P*(Real.exp t)^2)^j) (pow_le_pow_left₀ (by unfold n; positivity) (hx'.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hu) hf _) hP.le)) j)
    rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]; exact le_of_eq (by push_cast; ring_nf)
  have hH : Real.exp (A'+D-X*t^2)*Real.exp (2*j*t)*Real.exp (k*t) ≤ Real.exp (A'+D+D')*Real.exp (-y*t^2) := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; unfold D'
    rw [show X=2*y by unfold y; ring]; field_simp; nlinarith [sq_nonneg (2*(j:ℝ)+k-2*y*t)]
  change _/lens₀ _ _ * U'^k ≤ H*(Real.exp (-y*t^2)/ _); rw [← mul_div_assoc,div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ hP'
  change Z' * Real.exp _* b (B+t)*_≤_
  have hk : U'^k ≤ Real.exp (k*t) := by
     rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (zero_le_one.trans hu) (by unfold U'; rw [add_comm]; exact Real.add_one_le_exp _) _
  apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hF (show 0≤Z'*Real.exp (A'+D-X*t^2) by positivity)) hk (by positivity) (by positivity))
  calc
    _ = (Z'*P^j)*(Real.exp (A'+D-X*t^2)*Real.exp (2*j*t)*Real.exp (k*t)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hH (show 0≤Z'*P^j by positivity)).trans_eq (mul_assoc ..).symm
end YM.ConnectedActivityE6.Blaze.Flux
