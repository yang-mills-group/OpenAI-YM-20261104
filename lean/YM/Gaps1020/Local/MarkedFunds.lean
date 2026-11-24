import YM.Gaps1020.Local.MarkedSlices
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
-- all sectors jointly. Fuel price inflation struct at the H.support
-- encounter (meets the anchor invariant). No `root` hit assumption here.
-- R^(M+1) extra premium for rare marks/path; already in inflated costs:
def levyMix (M:ℕ) (p:H.ThinP)(ρ:ℝ):=1+ρ^(M+1)*(if 1≤Cash.numP p.val then 1 else 0) + ρ^(M+1)*(if (till s:ℝ) ≤ H.shapeW p.val then 1 else 0)
variable (N:Captain H j C' d v Y A b r B q k χ)(p:H.ThinP)(U:Team R)
    (hP:Healthy (Pressure.temp s) (H.smallAt p) (V x))(hM:Mode V x j v)
def feeMix (U:Team R)(ρ Z:ℝ)(M:ℕ):= (levyMix M p ρ*(Z^(blaze p.val).card))* (ρ^p.val.card * earnedBy p.val U N.conduit k)
def reserveBy (U:Team R)(ρ Z:ℝ)(M:ℕ):= (packets j M M * B)*feeMix N p U ρ Z M
def slotMix (ρ Z:ℝ)(M:ℕ)(i:Orders M):= reserveBy N p U ρ Z M*(ρ^i.val)⁻¹
variable {Z:ℝ}
lemma levies (M:ℕ)(p:H.ThinP)(ρ:ℝ)(h:0≤ρ): 1 ≤ levyMix M p ρ:= by unfold levyMix; split_ifs <;> first | positivity | linarith [pow_nonneg h (M+1)]
lemma fee0 (Z:ℝ)(hr:0≤ρ)(hz:0≤Z) (M:ℕ):0≤ feeMix N p U ρ Z M:=by unfold feeMix; exact mul_nonneg (mul_nonneg (zero_le_one.trans (levies _ _ _ hr)) (pow_nonneg hz _)) (mul_nonneg (pow_nonneg hr _) (earns ..))
lemma reserve0 (Z:ℝ)(hr:0≤ρ)(hz:0≤Z) (M:ℕ): 0≤ reserveBy N p U ρ Z M := mul_nonneg (mul_nonneg (zero_le_one.trans (package ..)) N.balance) (fee0 N p U _ hr hz _)
private lemma below {ι:Type} [Fintype ι] (f:ι→ℝ) (g:ι→ℕ)(M:ℕ):
    (∑ i∈ (Finset.univ.filter (fun i=> ¬ M≤g i)), f i)=∑ k∈range M,∑ i∈ (univ.filter (fun i=>g i=k)), f i:= by
  simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i hi
  symm; rw [Finset.sum_ite_eq]; simp [mem_range, not_le]
private lemma mint {K:ℕ}(p:Molecule S)(hN : p.card ≤ K)(h2:2 ≤ ρ) (F:Finset (Assign p M))(m:ℕ)(he:∀ π∈ F,m≤ Thermal1020.degree p π) :
     ∑ π∈ F,ratesheet p π j ρ ≤ (packets j K M*ρ^p.card)*(ρ^m)⁻¹:=by
  have hpos:0<ρ:=by linarith
  have hp:1≤ρ:=by linarith
  let r:= overhead j M; have hr:1≤r:= overhead_bound ..
  let w:= p.card; have hK:w≤K:= hN
  let i (x:ℕ):=(1+(1+(x:ℝ)))^j
  have hu : i w ≤ i K:=by unfold i; gcongr
  have h : ∀ π∈F, ratesheet p π j ρ*ρ^m≤ r^w * i w * ρ^w:= by
    intro π hπ
    let d:= ∑ i:↥p,((π i).val-1);
    have hD: m ≤ d+w:=le_trans (he _ hπ) (le_trans (Finset.sum_le_sum (s:= (univ:Finset (↥p))) (g:=fun i=> (π i).val-1+1) (fun i _=>by omega)) (by rw [sum_add_distrib]; simp [d,w]))
    calc
      _= r^w* i w * ((ρ^d)⁻¹ * ρ^m):=by unfold ratesheet; rw [Finset.prod_mul_distrib, Finset.prod_const,card_univ,Fintype.card_coe,Finset.prod_pow_eq_pow_sum,inv_pow]; unfold r i d w; ring
      _≤ _ := mul_le_mul_of_nonneg_left (by
        rw [mul_comm,← div_eq_mul_inv,div_le_iff₀ (pow_pos hpos _),← pow_add]; exact pow_le_pow_right₀ hp (by omega)) (by unfold i; positivity)
  rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hpos _),sum_mul]
  have hf : F.card ≤ (M+2)^w:= Finset.card_le_card (Finset.subset_univ F) |>.trans (by rw [card_univ]; unfold Assign; simp [w])
  apply le_trans (Finset.sum_le_sum h)
  rw [sum_const,nsmul_eq_mul]; calc
    _≤ ((M+2)^w:ℝ)*(r^w*i w*ρ^w):=mul_le_mul_of_nonneg_right (by exact_mod_cast hf) (by unfold i; positivity)
    _=(((M+2:ℕ):ℝ)*r)^w*i w*ρ^w:=by push_cast; rw [mul_pow]; ring
    _ ≤ _ := by unfold packets; unfold r i at *; gcongr; first | exact overhead_bound _ _|exact one_le_mul_of_one_le_of_one_le (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) M]) (overhead_bound _ _)
include hP hM N
variable (h : HasClutch N.conduit A)(hρ:charge Q L s r j (till s) ≤ ρ⁻¹)(h2:2 ≤ρ)(hZ:ρ^(M+1) ≤ Z)
    (hf: Flock H N.conduit A B k)(ha:awake H p U)
include ha hf
private lemma retained : Brush j (B*earnedBy p.val U N.conduit k) 1 (preserved H χ p U ∘ V) x := by
  let w:= emptyTeamData U p.val
  let f (q:Greenbelt.Reserve S)(u:E):= teamWeightFringe (prism T s χ o.K (V u) (allot q)) p.val R U w Q.table W o.a Q.halo
  let E₀:=earnedBy p.val U N.conduit k
  have h(q:Greenbelt.Reserve S): Brush j (B*E₀) 1 (f q) x:=by
    let F := allot q; let X:=prism T s χ o.K (V x) F
    apply Brush.shimmy _ (teamWeightRainbow (X:=X) p.val U w N.oboe rfl rfl rfl p.prop.2 hP hM rfl)
    unfold teamWeightShelter; simp_rw [show ∀ y,(vary X (V y)).B=radiusB s from fun _=>rfl,if_pos (show Ac.Spark (areas R T Q.halo (radiusB s)) p.val ∧ troupe T R Q.halo (radiusB s) p.val from ⟨ha.1,ha.2.1⟩)]
    let P t:= preps (vary X (V t)) (roster p.val)
    let a i v:= teamWeightBars p.val (podium S G (H.smallAt p) (radiusB s)) ((P v).taggedL i) R U w Q.table W o.a Q.halo
    apply Captain.avgBrush a; intro i
    let X':= (planted X p.val).taggedL i; have hm:=show X'.manifest from planted_valid X p.val
    let A' (v:E) := teamWeightBars p.val (podium S G (H.unionP p.val) (radiusB s)) (vary X' (V v)) R U w Q.table W o.a Q.halo
    apply Brush.shimmy (f:=A') _ (Eventually.of_forall fun j=> (teamWeightSpices p.val U _ H X rfl (V j) (V j) (fun _ _ _=>rfl) hP p.prop.2 i).symm)
    obtain ⟨g,hg,hK,h⟩:= hf.teams E F X' V x U p.val ha.2.2 rfl hm rfl rfl hP ha.2.1 ha.1 hM rfl
    have hD:= N.oboe.flow F X' rfl rfl rfl hm E V x rfl hM
    exact ((teamMultiplied H rfl hm rfl hD N.oboe.conduit N.oboe.mode p.val U w (fun _=>contDiff_const) _).1.buds g hg zero_le_one hK (Eventually.of_forall h)).shimmy (teamUnfoldBars H rfl hm rfl hD N.oboe.conduit N.oboe.mode p.val U w (fun _=>contDiff_const))
  unfold preserved Function.comp writtenBy; simp_rw [if_pos ha]
  letI: Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  exact Captain.avgBrush f _ x h
omit hP hM N hf ha in
private lemma rareLevy (hm: ¬narrowMix H M p U)(hr:1≤ ρ)(hZ:ρ^(M+1) ≤ Z):
    ρ^(M+1) ≤ levyMix M p ρ*Z^(blaze p.val).card*ρ^p.val.card:=by
    have h₀ : 0 ≤ ρ:= zero_le_one.trans hr
    have hz:1≤Z:= (one_le_pow₀ hr).trans hZ
    have hp:0≤ Z:=zero_le_one.trans hz
    have ht:1≤ levyMix M p ρ:= levies M p _ h₀
    by_cases h:blaze p.val=∅
    swap; · apply le_trans (b:=Z^(blaze p.val).card) (hZ.trans (le_self_pow₀ hz (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)).ne'))
            exact (le_mul_of_one_le_left (pow_nonneg hp _) ht).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr))
    rw [h,card_empty,pow_zero,mul_one]
    by_cases hL : (others U p.val).card ≤ M
    · have he : 1≤ Cash.numP p.val ∨ (till s:ℝ) ≤ H.shapeW p.val :=by by_contra! hy; exact hm ⟨h,Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hy.1),hy.2,hL⟩
      have ha: ρ^(M+1) ≤ levyMix M p ρ:=by unfold levyMix; rcases he with h|h <;> simp_rw [if_pos h] <;> split_ifs <;> linarith only [pow_nonneg h₀ (M+1)]
      exact ha.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr))
    apply le_trans (b:=ρ^p.val.card) (pow_le_pow_right₀ hr (le_trans (Nat.succ_le_of_lt (lt_of_not_ge hL)) (Finset.card_le_card sdiff_subset))); exact le_mul_of_one_le_left (by positivity) ht
include h hρ h2 hZ
omit ha
lemma debts (i:Orders M): Brush j (slotMix N p U ρ Z M i) 1 (sliceMix H χ M p U i ∘ V) x:=by
  have hA:0<ρ:=by linarith
  have hR:1≤ρ:=by linarith
  have hv:1≤Z:= (one_le_pow₀ hR).trans hZ
  have h₀ : 0 ≤ slotMix N p U ρ Z M i:= mul_nonneg (reserve0 N p U Z hA.le (zero_le_one.trans hv) M) (by positivity)
  by_cases ha : awake H p U; swap; · exact Brush.zi (Eventually.of_forall fun u=>sleepy p U ha (V u) i) h₀ zero_le_one
  let p₀ := B*earnedBy p.val U N.conduit k; have hp₀ : 0≤ p₀:=mul_nonneg N.balance (earns ..); have ht : 1≤ packets j M M:= package ..
  by_cases he : narrowMix H M p U
  swap; · have he'(k V):shortMix H χ M p U k V=0:= if_neg he
          by_cases hI: i.val=M+1
          · apply Brush.shimmy ((retained N p U hP hM hf ha).climb ?_ le_rfl) (Eventually.of_forall fun u=>by simp_rw [Function.comp_def, sliceMix,if_pos hI,he',Finset.sum_const_zero,sub_zero])
            let z:=levyMix M p ρ*Z^(blaze p.val).card*ρ^p.val.card
            have hz:ρ^(M+1)≤z:=rareLevy p U he hR hZ
            unfold slotMix; rw [hI,← div_eq_mul_inv,le_div_iff₀ (pow_pos hA _),mul_comm]; change ρ^(M+1)*p₀≤_
            calc
              _ ≤ z*p₀ := mul_le_mul_of_nonneg_right hz hp₀
              _ ≤ packets j M M*(z*p₀) := le_mul_of_one_le_left (mul_nonneg ((pow_nonneg hA.le _).trans hz) hp₀) ht
              _= reserveBy N p U ρ Z M:=by unfold reserveBy feeMix z p₀; ring
          exact Brush.zi (Eventually.of_forall (fun v=>(show sliceMix H χ M p U i _ = _ from if_neg hI).trans (he' _ _))) h₀ zero_le_one
  let q':= others U p.val; let f π u:= writtenBy H χ p U (assignment _ (π:Assign q' M)) (V u); let g:= Thermal1020.degree q' (M:=M)
  have hh i: Brush j (ratesheet q' i j ρ*p₀) 1 (f i) x:=by
    unfold f writtenBy; simp_rw [if_pos ha]
    let I(q:Greenbelt.Reserve S)(k:E):= teamWeightFringe (prism T s χ o.K (V k) (allot q)) p.val R U (assignment q' i) Q.table W o.a Q.halo
    letI:Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    exact Captain.avgBrush I _ x (fun j=> teamFringePower (X:=prism T s χ o.K (V x) (allot j)) p.val U h N.oboe rfl rfl rfl hM rfl p.prop.2 hP (remainingCost he ha) ha.2.1 ha.1 he.2.2.1.le hρ h2 i hf ha.2.2)
  have hx (T:Finset (Assign q' M))(he':∀ j∈ T,i.val ≤ g j): Brush j (slotMix N p U ρ Z M i) 1 (fun u=> ∑ j∈ T,f j u) x:=by
    apply (Brush.spree _ f _ zero_le_one (fun q (_:q∈T)=>hh _)).climb _ le_rfl
    rw [← Finset.sum_mul]; have h:= mint (j:=j) q' he.2.2.2 h2 T i.val he'
    apply le_trans (mul_le_mul_of_nonneg_right h hp₀); unfold slotMix; rw [mul_right_comm]
    gcongr; unfold reserveBy feeMix levyMix; rw [he.1,card_empty,pow_zero,mul_one,he.2.1, if_neg (by norm_num : ¬1≤(0:ℕ)),if_neg (not_le.mpr he.2.2.1)]; simp only [mul_zero,add_zero,one_mul]
    calc
       _ ≤ packets j M M*ρ^p.val.card*p₀:=by gcongr; exact sdiff_subset
       _ = _ :=by unfold p₀; ring
  by_cases hi : i.val=M+1
  · let p':= univ.filter (fun j=>i.val ≤ g j)
    apply (hx p' (fun i h=> (mem_filter.mp h).2)).shimmy
    let X k:= prism T s χ o.K (V x) (Greenbelt.allot (S:=S) k)
    have h(i):= teamFringeTogether p.val U N.oboe (X:=X i) rfl rfl rfl hM rfl p.prop.2 hP M
    have hp' : (fun u=> ∑ q,f q u)=ᶠ[𝓝 x] preserved H χ p U ∘ V:=by
      filter_upwards [eventually_all.mpr h] with y hv
      unfold preserved f writtenBy; simp_rw [Function.comp_def,if_pos ha,Pond.likely]; rw [← Finset.mul_sum,Finset.sum_comm]; exact congr_arg _ (sum_congr rfl fun i _=>hv i)
    filter_upwards [hp'] with y hy; rw [Function.comp_apply] at *; rw [sliceMix,if_pos hi]; simp_rw [shortMix,if_pos he]; rw [← hy]
    change (∑ j,f j y) - (∑ k∈range (M+1),∑ i∈ (univ.filter (fun i=>g i=k)), f i y)=_; rw [← below (fun j=>f j y) g (M+1)]; unfold p'; rw [hi]; apply sub_eq_of_eq_add; exact (Finset.sum_filter_add_sum_filter_not ..).symm
  exact (hx (univ.filter (fun j=>g j=i.val)) (fun j hj=>((mem_filter.mp hj).2 : g j=i.val).symm.le)).shimmy (Eventually.of_forall fun v=> by change sliceMix H χ M p U i _ = _; rw [sliceMix,if_neg hi,shortMix,if_pos he])
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
