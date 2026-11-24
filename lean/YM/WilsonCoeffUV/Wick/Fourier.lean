import YM.WilsonCoeffUV.Flat.PoleRate
import YM.PertExtension.PacketFourier
import YM.Pert.Fourier.Fee
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Fourier
/-!
# The full filtered free covariance (for Wick letters ONLY).

Riemann-limit massless G in Train.levelD gauge on the infinite cover.
For the optional finite-period approximation lemma use ordinary discrete
periods with SINGLE zero harmonic thrown away. This is not the
orbifold perturbative regulator. Equivalence here is for Wick jets at
order zero. No phase/tags. Norm convention: absolute supremum over points
incl origin and ALL lifts, not an assertion of exponential pricing on a
massless propagator. Use the latter only for the fluctuation covariance.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Extension.UV.Linear
open Next.Rank.Radian PertExtension.LatticePT.Converter MeasureTheory
open scoped Topology ContDiff BigOperators ComplexConjugate Classical
variable {G:Gauge}{j k m N:ℕ}{n:Side} {s C:ℝ}

abbrev pall (x:E4):= addr n (mark n x)
lemma cloud (n:Side){x:E4}(he:pall (n:=n) x≠0) : (n.val:ℝ)⁻¹≤‖pall (n:=n) x‖:= Pert.Cellular.visit_floor n x he
lemma roof (n:Side) (x:E4)(hx:pall (n:=n) x≠0): ‖x‖ ≤ 5*‖pall (n:=n) x‖:= by
   let p:=pall (n:=n) x
   have ht:dist p x ≤ 4* (n.val:ℝ)⁻¹ := rock _
   have hp : (n.val:ℝ)⁻¹ ≤ ‖p‖:= cloud n hx
   have hu: ‖x‖-‖p‖≤ dist p x := by rw [dist_comm, dist_eq_norm]; exact norm_sub_norm_le ..
   change ‖x‖≤ _ * ‖p‖; linarith
lemma pall_tends (x:E4) : Tendsto (fun n:Side=>pall (n:=n) x) atTop (𝓝 x):=by
   have ht : Tendsto (fun n:Side=> (n.val:ℝ)⁻¹) atTop (𝓝 0) := by
     have hp : Tendsto Subtype.val (atTop:Filter Side) (atTop:Filter ℕ):= tendsto_atTop.mpr (fun k=> (eventually_ge_atTop (⟨k+1,k.succ_pos⟩:Side)).mono fun n hn=> Nat.le_trans (by omega) (show k+1≤ n.val from hn))
     exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hp)
   rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (Eventually.of_forall fun _=> rock x) (show Tendsto (fun n:Side=> 4*(n.val:ℝ)⁻¹) atTop (𝓝 0) from by simpa only [mul_zero] using ht.const_mul 4)

def tableU (f:E4→ℂ)(n:Side) := ((n.val:ℝ)⁻¹)^4 • ∑ i:Site n,f (addr n (lift i))
structure visitP (f:E4→ℂ) (S:ℝ): Prop where
    shuts x: x∉unitbox → f x=0
    scars x : ‖f x‖ ≤ S * (‖x‖^2)⁻¹
lemma scanned {f:E4→ℂ}(h:visitP f C)(n:Side): tableU f n=scansP n f 1:=by
   unfold tableU scansP; apply congr_arg
   let R:= (Finset.univ (α:=Site n)).image lift
   have he: R⊆ room n 1 := by
       rintro x hx; obtain ⟨i,_,rfl⟩:= Finset.mem_image.mp hx; exact addressBW _ _ (show ‖addr n (lift i)‖≤ (↑(1:ℕ):ℝ) from by simpa only [Nat.cast_one] using point_cover ((centered_lift n _).mpr (congr_arg lift (wrap_lift i))))
   rw [← Finset.sum_subset he]
   · unfold R; rw [Finset.sum_image]; exact (show Injective (lift (n:=n)) from fun i j h=> by rw [← wrap_lift i,← wrap_lift j,h]).injOn
   intro i _ hi; exact h.shuts _ (fun v=> hi (Finset.mem_image.mpr ⟨wrap n _,Finset.mem_univ _,(centered_lift ..).mp v⟩))
lemma scanned_form {f:E4→ℂ}(h:visitP f C)(n:Side): Integrable (fun x=>f (pall (n:=n) x)) ∧ (∫ x,f (pall (n:=n) x))=tableU f n:=by
   rw [scanned h]; exact grid_born n f 1 (fun x hx=> h.shuts x (by
    have hr : 1<‖x‖:=by (exact_mod_cast hx)
    exact fun he=>not_lt_of_ge (point_cover he) hr))
lemma scanned_wealth {f:E4→ℂ}(h:visitP f C)(hc:0≤C)(n:Side): ∀ᵐ x:E4, ‖f (pall (n:=n) x)‖ ≤ 25*C * Pert.Cellular.spike 3 x:=by
   refine shore.mono fun x ⟨_,hx⟩=>?_
   let p:=pall (n:=n) x
   change ‖f p‖ ≤ _
   have hv : 0≤25*C*Pert.Cellular.spike 3 x := mul_nonneg (by positivity) (indicator_nonneg (fun x _=>show 0≤ (‖x‖^2)⁻¹ from by positivity) x)
   by_cases ht:p∈unitbox; swap; · rw [h.shuts _ ht,norm_zero]; exact hv
   have hw :‖f p‖≤ C*(‖p‖^2)⁻¹:= h.scars _
   by_cases hu:p=0; · apply hw.trans; rw [hu,norm_zero]; simpa using hv
   have hp:= point_cover ht; have he:‖x‖ ≤ 5*‖p‖:= roof n _ hu
   unfold Pert.Cellular.spike; rw [indicator_of_mem (show x∈ball 0 (2*3) from mem_ball.mpr (by rw [dist_zero_right]; linarith))]; rw [mul_comm (25:ℝ),mul_assoc]
   apply le_trans hw; apply mul_le_mul_of_nonneg_left _ hc
   have hy : ‖p‖ > 0:=norm_pos_iff.mpr hu; have hq : ‖x‖ > 0:=norm_pos_iff.mpr hx
   rw [←one_div, ←div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [he,hy,hq]

def billet := (25:ℝ)*∫ x:E4,Pert.Cellular.spike 3 x
lemma bill_good : 0≤billet := by unfold billet; exact mul_nonneg (by norm_num) (integral_nonneg (indicator_nonneg (fun x _=>show 0≤ (‖x‖^2)⁻¹ from by positivity)))
lemma charge {f:E4→ℂ}(h:visitP f C)(hc:0≤C)(n:Side): ‖tableU f n‖ ≤ billet*C:=by
    rw [← (scanned_form h n).2]; unfold billet
    apply (norm_integral_le_of_norm_le ((Pert.Cellular.spike_int 3).const_mul (25*C)) (scanned_wealth h hc n)).trans
    rw [integral_const_mul]; exact (le_of_eq (by ring))
lemma released {f:E4→ℂ}(h:visitP f C)(hc:0≤C)(p:∀ᵐ x:E4,ContinuousAt f x): Tendsto (tableU f) atTop (𝓝 (∫ x,f x)):=by
    refine Tendsto.congr' ?_ (f₂:= tableU f) (f₁:= fun n:Side=> ∫ x,f (pall (n:=n) x)) ?_
    · exact Eventually.of_forall (fun i=> (scanned_form h i).2)
    exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall (fun n=> (scanned_form h n).1.aestronglyMeasurable)) (Eventually.of_forall (fun n=>scanned_wealth h hc n)) ((Pert.Cellular.spike_int 3).const_mul (25*C)) (p.mono (fun x hx=> hx.tendsto.comp (pall_tends x)))

open Further.FreeCovariance.KP (mcast lit lit_mon)
open PhysicalNext.RankCovariance (circleRate circle_pos shift_rate)
def mκ (p:E4):Momentum:= mcast (circleRate • p)
lemma mnode (p: Site n): mκ (addr n (lift p)) = mon p:= by rw [mκ,shift_rate,lit_mon]
lemma mnode0 {p:Site n}: mon p=0 ↔ p=0:= by
    refine ⟨fun h=>?_,fun h=>h ▸ mon_zero⟩; by_contra he; obtain ⟨i,hi⟩:= step_picks p he; apply hi; rw [cell_step,h]; simp
lemma mcat x: lengthSq (mκ x) = circleRate^2*‖x‖^2:=by
    unfold lengthSq; simp_rw [mκ,mcast,Complex.norm_real]; rw [show circleRate^2*‖x‖^2= ‖circleRate • x‖^2 by rw [norm_smul,mul_pow,Real.norm_of_nonneg circle_pos.le],PiLp.norm_sq_eq_of_L2]
lemma mflow (x:E4): circleRate*‖x‖≤2 * ‖mκ x‖:=by
    have hh := (length_bounds (mκ x)).2
    rw [mcat x] at hh; nlinarith only [hh,circle_pos,norm_nonneg (mκ x),norm_nonneg x]
lemma mfall {x:E4}(h:x ≠ 0): mκ x≠0:=by intro he; have ht:= mflow x; rw [he,norm_zero,mul_zero] at ht; exact ht.not_gt (mul_pos circle_pos (norm_pos_iff.mpr h))
lemma mould {x:E4} (h:x∈unitbox): mκ x∈baseCube:=by
    refine ⟨(physical_iff _).mpr (fun _=>rfl),?_⟩; intro i; obtain ⟨a,b⟩:= h i
    change |2*Real.pi*x i|≤_; have hp:=Real.pi_pos; rw [abs_le]; constructor <;> nlinarith
lemma mfloat : Continuous mκ := by unfold mκ mcast; fun_prop
lemma mzero : mκ 0=0:= by unfold mκ mcast; simp; rfl

-- throw zero harmonic at coefficient lattice, test only horizontal meaning below

def loomM (k:ℝ)(v:Train j)(p:Momentum): Frequency 1 1:= if p=0 then 0 else fieldD 1 k v p
def frost (k:ℝ)(v:Train j)(a b:TypeFace 1)(x:Cover)(z:E4):ℂ:= unitbox.indicator (fun p=> mode (mκ p) x * loomM k v (mκ p) a b) z
lemma faresH (k:ℝ)(hj:4≤j): ∃ C:ℝ,0<C ∧ ∀ (v:Train j) (a b:TypeFace 1) (x:Cover),visitP (frost k v a b x) C:=by
    obtain ⟨η,c,hη,hc,H⟩:= Train.bulb_budget k hj (fun i:Train j × Axis=> i.1) (fun i=>i.2)
    let u:= Next.Free.meter.low; have he:0<u:=Next.Free.meter.low_pos
    let B:=c/(u^2*circleRate^2); have hP : 0<circleRate := circle_pos
    refine ⟨B,by unfold B; positivity,fun v a b x=> ⟨fun p h=>indicator_of_notMem h _,?_⟩⟩; intro z; by_cases h:z∈unitbox; swap; · rw [frost,indicator_of_notMem h,norm_zero]; unfold B; positivity
    rw [frost,indicator_of_mem h]
    by_cases ht:z=0; · rw [ht,mzero,loomM,if_pos rfl,Matrix.zero_apply,mul_zero,norm_zero]; positivity
    have hp := mould h; rw [norm_mul,mode_real _ _ hp.1,one_mul, loomM, if_neg (mfall ht), fieldD,mask_value]; split; swap; · rw [norm_zero]; unfold B; positivity
    next =>
      set s:= axisEquiv.symm a
      let p:=mκ z; let t:=divisor v.mass p
      have hw := (divisor_real_bounds v.mass (base_subset_realCube zone_pos hp)).1
      have hy:= calc
         u^2*circleRate^2*‖z‖^2 = u^2*lengthSq (mκ z):= by rw [mcat,mul_assoc]
         _ ≤ ‖t‖:= hw.trans (Complex.re_le_norm _)
      rw [scaleD,Train.D_bulb k v (base_subset_realCube zone_pos hp) (mfall ht)]; simp only [PNat.val_ofNat, Nat.cast_one,one_pow, inv_one, one_mul,norm_div]
      have hf :0<‖z‖:= norm_pos_iff.mpr ht
      calc
        _ ≤ c / (u^2*circleRate^2*‖z‖^2) := by
           have hb : ‖Train.bulb k v (mκ z) s‖≤c:= by simpa using (H (v,s)).bound (mκ z) (mem_cube_real (base_subset_realCube hη hp) hη)
           gcongr
        _ = _ := by unfold B; field_simp
lemma frost_dense (k:ℝ)(h:4≤j)(v:Train j)(a b:TypeFace 1)(x:Cover) : ∀ᵐ p:E4, ContinuousAt (frost k v a b x) p:=by
    set i:=axisEquiv.symm a
    have hf (p:E4)(ht:p∈unitbox)(hz:p≠0): frost k v a b x p=mode (mκ p) x*(if a=b then Train.bulb k v (mκ p) i/divisor v.mass (mκ p) else 0):=by rw [frost,indicator_of_mem ht,loomM,if_neg (mfall hz),fieldD,mask_value,scaleD_one,Train.D_bulb k v (base_subset_realCube zone_pos (mould ht)) (mfall hz)]
    have hv p (h:p∈opencube):p∈unitbox:= fun i=>⟨(h i).1,(h i).2.le⟩
    filter_upwards [shore] with z hz
    obtain ⟨hc,he⟩:=hz
    rcases hc with hx|hx
    · have hp : ∀ᶠ p in 𝓝 z, p∈opencube := by
         have hs:IsOpen opencube:= by
            have hx : opencube= (PiLp.homeomorph 2 (fun _:Axis=>ℝ)) ⁻¹' Set.pi Set.univ (fun i: Axis=>Ioo (-1/2:ℝ) (1/2)):=by ext x; simp only [opencube,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_Ioo,Set.mem_univ, forall_const]; rfl
            rw [hx]; exact (isOpen_set_pi Set.finite_univ fun i hi=>isOpen_Ioo).preimage (PiLp.homeomorph ..).continuous
         exact hs.mem_nhds hx
      let M p:= mode (mκ p) x
      have hM:ContinuousAt M z := (((show Differentiable ℂ (fun p : Momentum=>mode p x) by unfold mode; fun_prop).continuous).comp mfloat).continuousAt
      obtain ⟨η,c,hη,_hc,H⟩:= Train.bulb_budget k h (fun _ : Unit=> v) (fun _=>i)
      have hc:= mould (hv z hx)
      have hB: ContinuousAt (fun p=> Train.bulb k v (mκ p) i) z:= ContinuousAt.comp (f:=mκ) (g:=fun z=> Train.bulb k v z i) (show ContinuousAt _ _ from ((H Unit.unit).hol _ (mem_cube_real (base_subset_realCube hη hc) hη)).continuousAt) mfloat.continuousAt
      obtain ⟨η,c,hη,_,H⟩:= divisor_control (fun _:Unit=>v.mass)
      have hD: ContinuousAt (fun p=>divisor v.mass (mκ p)) z := ((H Unit.unit).hol (mκ z) (mem_cube_real (base_subset_realCube hη hc) hη)).continuousAt.comp mfloat.continuousAt
      have HH : ContinuousAt (fun p=>M p*(if a=b then Train.bulb k v (mκ p) i/divisor v.mass (mκ p) else 0)) z:= by
         apply hM.mul; split; exact hB.div hD (divisor_ne _ (base_subset_realCube zone_pos hc) (mfall he)); exact continuousAt_const
      refine HH.congr ?_; filter_upwards [hp,eventually_ne_nhds he] with p hx hz; exact (hf p (hv p hx) hz).symm
    have he': IsClosed closedunit:= by
       have hp : closedunit = (PiLp.homeomorph 2 (fun _:Axis=>ℝ)) ⁻¹' Set.pi Set.univ (fun i: Axis=>Icc (-1/2:ℝ) (1/2)):=by ext x; simp only [closedunit,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_Icc,Set.mem_univ, forall_const]; rfl
       rw [hp]; exact (isClosed_set_pi fun i hi=>isClosed_Icc).preimage (PiLp.homeomorph ..).continuous
    refine (continuousAt_const (y:=(0:ℂ))).congr ?_; filter_upwards [he'.isOpen_compl.mem_nhds hx] with p hp; exact (indicator_of_notMem (fun (h:p∈unitbox)=> hp (fun i=>⟨(h i).1.le,(h i).2⟩)) _).symm

def finiteStar (k:ℝ)(v:Train j)(x:Cover)(a b:TypeFace 1): Side → ℂ:= tableU (frost k v a b x)
def infiniteStar (k:ℝ)(v:Train j)(x:Cover)(a b:TypeFace 1): ℂ:= ∫ y:E4,frost k v a b x y
lemma starExit (k:ℝ)(v:Train j)(x:Cover)(a b:TypeFace 1)(h:4≤j): Tendsto (finiteStar k v x a b) atTop (𝓝 (infiniteStar k v x a b)):=by obtain ⟨C,c,H⟩:=faresH k h; exact released (H ..) c.le (frost_dense k h ..)
lemma starFumes (k:ℝ)(h:4≤j): ∃C:ℝ,0≤C ∧ ∀ (v:Train j) x a b,(∀ n, ‖finiteStar k v x a b n‖≤ C)∧ ‖infiniteStar k v x a b‖≤ C:=by
  obtain ⟨C,hC,H⟩:= faresH k h
  refine ⟨billet*C,mul_nonneg bill_good hC.le,fun v x a b=> let hp n:=charge (H v a b x) hC.le n; ⟨hp,le_of_tendsto (Tendsto.norm (starExit k v x a b h)) (Eventually.of_forall hp)⟩⟩

abbrev priceΩ (A:Levels G) (k:ℝ) (m i:ℕ):ℝ:= Dcost k (A.clock.J i)/(location A i m).mass.val
lemma starFareGap (k:ℝ)(hj:4≤j): ∃ C:ℝ,0≤C ∧ ∀ (G:Gauge) (A:Levels G) (m i N M:ℕ), (A.clock.J m = j) → (m ≤ i) → (i ≤ N) → (i ≤ M) →  ∀ x a b, let P:=location A N m; let Q:= location A M m; visitP (frost k P a b x -frost k Q a b x) (C * priceΩ A k m i):=by
    obtain ⟨F,hF,H⟩:= pole_tail k j hj
    let W:= 2 / circleRate; have ht:0<W:=by unfold W; apply div_pos (by norm_num) circle_pos
    refine ⟨F*W,(mul_pos hF ht).le,?_⟩
    intro G A m i N M hj hv hp hq x a b P Q; let T:= priceΩ A k m i; have hh : 0< T:= div_pos (Dcost_pos ..) (side_pos _)
    have hh' :0≤ F*W*T:=mul_nonneg (by positivity) hh.le
    have hz (y:E4)(hy:y∉unitbox):(frost k P a b x -frost k Q a b x) y=0:= by rw [Pi.sub_apply,frost,frost,indicator_of_notMem hy,indicator_of_notMem hy,sub_zero]
    refine ⟨hz,?_⟩
    intro y
    change _≤ F*W*T*(‖y‖^2)⁻¹
    by_cases hu : y∈unitbox; swap; · rw [hz y hu,norm_zero]; positivity
    rw [Pi.sub_apply, frost,frost,indicator_of_mem hu,indicator_of_mem hu]
    by_cases he:y=0; · rw [he,mzero]; simp [loomM]
    rw [← mul_sub,norm_mul,mode_real _ _ (mould hu).1,one_mul,loomM,if_neg (mfall he), loomM,if_neg (mfall he),fieldD,fieldD,mask_value,mask_value]; split; swap; · rw [sub_zero,norm_zero]; positivity
    next hx=>
       simp only [scaleD_one]; refine le_trans (H A m i N M hj hv hp hq _ _ (mould hu) (mfall he)) ?_
       have ht:=mflow y; have hy : 0<‖y‖:= norm_pos_iff.mpr he; have hg : 0<‖mκ y‖:= norm_pos_iff.mpr (mfall he)
       have hf : ‖y‖≤1:=point_cover hu
       change F*T*‖mκ y‖⁻¹ ≤ _; rw [mul_right_comm F W,mul_assoc (F*T) W]
       apply mul_le_mul_of_nonneg_left _ (by positivity)
       unfold W; field_simp
       rw [le_div_iff₀ circle_pos]; nlinarith only [ht,hy,hf,mul_nonneg circle_pos.le (show 0 ≤ ‖y‖-‖y‖^2 by nlinarith only [hy,hf])]
lemma starLifeGap (k:ℝ)(hj:4≤j) : ∃ C:ℝ,0≤C ∧ ∀ (G:Gauge) (A:Levels G) (m i N M:ℕ), (A.clock.J m = j) → (m ≤ i) → (i ≤ N) → (i ≤ M) → ∀ x a b, let P:=location A N m; let Q:=location A M m; let D:= C*priceΩ A k m i; (∀ n, ‖finiteStar k P x a b n-finiteStar k Q x a b n‖≤D)∧ ‖infiniteStar k P x a b-infiniteStar k Q x a b‖≤D := by
    obtain ⟨C,hc,H⟩:=starFareGap k hj
    refine ⟨_,mul_nonneg bill_good hc,?_⟩; intro G A m i N M h p q e x a b P Q D; subst j
    let t:= priceΩ A k m i; have ht:0≤t:=(div_pos (Dcost_pos ..) (side_pos _)).le
    have hh n:‖finiteStar k P x a b n-finiteStar k Q x a b n‖ ≤ D:= by
       unfold finiteStar; rw [show ∀ f g:E4→ℂ,tableU f n-tableU g n=tableU (f-g) n from fun f g=>by simp only [tableU, Pi.sub_apply,Finset.sum_sub_distrib, smul_sub],show D=billet*(C*t) from mul_assoc ..]; exact charge (H G A m i N M rfl p q e x a b) (mul_nonneg hc ht) _
    exact ⟨hh,le_of_tendsto (Tendsto.norm (Tendsto.sub (starExit k P x a b hj) (starExit k Q x a b hj))) (Eventually.of_forall hh)⟩
end YM.WilsonCoeffUV.Bank.Carp
