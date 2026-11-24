import YM.TraceExtension.Chart.Orr
/-!
# No physical scale power lost in the short slab replication

Numerical estimates for `widthSky` on arbitrary `Gondola` (note no fixed upper bound
on Vane.b). Use PostT to pay for a containing/octave width (multiple of the mesh to
combine lattice cells with margins). Adapt several proofs from the finer-stamp system
in TraceExtension/Prom/Orion/Nitre (there requires AllowedSky, topL as on their rank films)
and Chart/Orr (along Vane).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Stamps
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Cells Trace Trace.Terrace Terrace.Glade Trace.Over Next.Rank Next.Rank.Station Perch Glimmer Atlas
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{𝓛 : Ultrafilter (ℕ×ℕ)}{F:Extraction.Order}
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}

private lemma gain_limit (T:Levels G)(i:ℕ)(r L:ℝ)(h:1≤L)(hR:1≤r)(hf: gainSky T.S i r < i → ((T.S.block (gainSky T.S i r)).val:ℝ) ≤ L): T.S.a (gainSky T.S i r)/T.S.a i ≤ L*r:=by
   let k:= gainSky T.S i r; have he:k ≤ i:=gain_under ..;change T.S.a k / T.S.a i≤_
   rcases lt_or_eq_of_le he with he|he
   · have hp: T.S.a (k+1)/T.S.a i ≤ r:= (lt_of_not_ge (fun hz' => Nat.not_succ_le_self k (gain_fee he hz'))).le
     let l:ℝ:= (T.S.block k).val; have hL : 0<l:= Nat.cast_pos.mpr (T.S.block k).property; have h': T.S.a k/T.S.a i=l*(T.S.a (k+1)/T.S.a i):=by rw [T.S.a_step]; change _= l*(T.S.a k/l/T.S.a i); field_simp
     rw [h']; exact mul_le_mul (hf he) hp (div_nonneg (T.S.a_pos _).le (T.S.a_pos _).le) (zero_le_one.trans h)
   rw [he,div_self (T.S.a_pos _).ne']; exact one_le_mul_of_one_le_of_one_le h hR


lemma block_upper (A : Levels G) (hG:G.Simple) (θ:PostT A) : ∀ᶠ k:ℕ in atTop,
    ∀ i:ℕ, i ≤ k → ((A.S.block i).val:ℝ) ≤ A.clock.monitor k := by
  filter_upwards [(hrate A hG).eventually (Lyra_small 1 one_pos)] with k hk i hi
  exact (θ.bloom i).trans ((lypos A hG hi).trans (by simpa only [Lyra,oracle,pow_one] using! hk))

lemma inch_upper (A : Levels G)(hG:G.Simple)(θ:PostT A) : ∀ᶠ k:ℕ in atTop, ∀ b:ℝ, 0<b →
    A.S.a (widthSky A b k)/A.S.a k ≤ mag A b k * (A.clock.monitor k)^5 :=by
    have hz:= YM.UVNext.Annulus.opens_radius hG A (s:=1) le_rfl (show 0<(1/5:ℝ) by norm_num)
    filter_upwards [hz,block_upper A hG θ] with k hz hk b hb
    let X:=clim A k; let V:=A.clock.coverSize k; let M:=A.clock.monitor k;let r:=wheel A k
    have hV : (1:ℝ) ≤ V:= by exact_mod_cast (A.budget k).B_pos
    have hm : 1 ≤ M:= by rw [show M=bill 1 X from Atlas.fire_bill A k]; exact Glimmer.costed _ _ zero_le_one
    have hs : (V:ℝ)^10≤M:=by
       change 16*(1:ℝ)*(V:ℝ)^2 ≤ Station.mag A (1/5:ℝ) k at hz
       have hc:(V:ℝ)^2 ≤ Perch.bill (1/5) X:=by rw [← show Station.mag A (1/5) k=bill (1/5) X from Atlas.mag_bill ..]; have hv:0≤(V:ℝ)^2:=sq_nonneg _;linarith only [hz,hv]
       rw [show (10:ℕ)=2*5 from rfl,pow_mul]
       apply le_trans (pow_le_pow_left₀ (sq_nonneg _) hc _) _; rw [Glimmer.bills,show M=_ from Atlas.fire_bill A k]; norm_num; exact le_rfl
    let i:=widthSky A b k
    let w:= widthSky A b k; let j:= middleSky A b k
    have hg: 1 ≤ mag A b k:=Real.one_le_rpow hm hb.le
    have he i (_hp:widthSky A b k ≤ i)(hi:i < k): ((A.S.block i).val:ℝ) ≤ M:= hk i hi.le
    have hX:= widerSky A b k; have hx:= beforeSky A b k
    have hj : A.S.a j/A.S.a k ≤ M*(mag A b k*M^2):= gain_limit A k _ _ hm (one_le_mul_of_one_le_of_one_le hg (one_le_pow₀ hm (n:=2))) (fun H=> he _ hX H)
    have hw : A.S.a w/A.S.a j ≤ M*((V:ℝ)^10):= gain_limit A j _ _ hm (one_le_pow₀ hV (n:=10)) (fun H=> he w le_rfl (H.trans_le hx))
    rw [show A.S.a (widthSky A b k)/A.S.a k = A.S.a w/A.S.a j*(A.S.a j/A.S.a k) by field_simp [(A.S.a_pos j).ne']; rfl]
    apply (mul_le_mul (hw.trans (mul_le_mul_of_nonneg_left hs (zero_le_one.trans hm))) hj (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le) (mul_nonneg (zero_le_one.trans hm) (zero_le_one.trans hm))).trans
    unfold M; apply le_of_eq; ring

include C
variable (hq:Gondola F H J 𝓛 V Y) (h:G.Simple)
include h hq
local notation "A"=> C.path.levels
lemma log_hat : Tendsto (fun i=> LogZoom J i / (A).clock.hatBeta (V i|>.k)) atTop (𝓝 G.slopeConstant⁻¹):=by
    let P':= A;let k(i):=(V i).k;let Q:=Stern V; let B:=P'.clock.hatBeta;let m(i):= B (k i); let L:= Lyra (A);let g:= G.slopeConstant; have hg:0 < g := Gauge.slopeConstant_pos h
    let f(i:ℕ):=b_zoom V i;have hb'(i):0 < f i:= shine i
    have hx:Tendsto (fun i=> Real.log (f i)/m i) atTop (𝓝 0):=by
        refine squeeze_zero' ?_ ?_ (show Tendsto (fun i=> Gate (m i)/m i) atTop (𝓝 0) from Gate_calm.comp ((hrate A h).comp hq.growth))
        · filter_upwards [(grow_big hq h).eventually_ge_atTop 1] with i hi; exact div_nonneg (Real.log_nonneg hi) (bell ..|>.le)
        filter_upwards [hq.growth.eventually (titles P' h 1 zero_lt_one)] with i hi; apply div_le_div_of_nonneg_right _ (bell ..|>.le); apply Real.log_le_iff_le_exp (hb' i)|>.2
        have hv: f i ≤ Terrace.watch _ 1 (k i):= (show f i ≤ tilt_cap P' (k i) from tiltP _ ((hq.season i).1.high.2)).trans hi.2
        simpa only [Terrace.watch, one_mul] using hv
    have hz₁:Tendsto (fun i=>P'.S.scale (k i)/m i) atTop (𝓝 g⁻¹):=by
        have he(i): P'.S.scale (k i)/m i=(1-P'.clock.bar/m i)/g:=by
            have hb:m i=P'.clock.bar+g*P'.S.scale (k i):=rfl; have hx:= bell P' (k i); field_simp [show m i≠ 0 from hx.ne'];linarith only [hb]
        simp_rw [he]; have he:= ((tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:=P'.clock.bar)).div_atTop ((hrate P' h).comp hq.growth))).div_const g; simpa only[sub_zero,one_div] using! he
    have hT : Tendsto (fun i=> LogZoom J i/m i) atTop (𝓝 g⁻¹):=by
        have he(i): LogZoom J i/m i= P'.S.scale (k i)/m i- Real.log (f i)/m i:=by
             unfold LogZoom; rw [Real.log_inv,show J.r i = P'.S.a (k i)*f i from (hq.season i).2.symm, Real.log_mul (P'.S.a_pos _).ne' (hb' i).ne']; unfold Schedule.scale; rw[Real.log_inv];ring
        simp_rw [he]; simpa only[sub_zero] using! hz₁.sub hx
    exact hT

-- price of the one power of log (actually can be made log^ε for every ε>0 on those fields)
lemma overhang (θ:PostT C.path.levels) :
    let w i := widthSky (A) (V i|>.b) (V i|>.k)
    ∀ᶠ i:ℕ in atTop,
      (0 < w i ∧ 20*C.S.a (w i) < C.S.a (w i-1) ∧
            C.S.a (w i-1) < J.r i*LogZoom J i/32) := by
  intro w
  let A':= C.path.levels
  let k (i:ℕ) := (V i).k; let b i:= (V i).b; let L:= LogZoom J
  let m i:= (A').clock.hatBeta (k i); let M i:= (A').clock.monitor (k i)
  have he : Tendsto m atTop atTop:= (hrate A' h).comp hq.growth
  have hv : ∀ᶠ i in atTop, C.S.a (w i) ≤ J.r i*M i^5 := by
    filter_upwards [hq.growth.eventually (inch_upper A' h θ)] with i hi
    have ht:=(hq.season i).1.high.1
    have hB:0<b i:= lt_trans (by norm_num) ht
    have hU:= (div_le_iff₀ (A'.S.a_pos _)).mp (hi _ hB)
    have hS:J.r i= C.S.a (k i)*mag A' (b i) (k i):=(hq.season i).2.symm
    rw [hS]
    exact hU.trans_eq (by change mag A' (b i) (k i)*M i^5*C.S.a (k i)=_; ring)
  have hM: Tendsto (fun i=> M i) atTop atTop := by
    exact (Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp he))))
  have hF:∀ᶠ i in atTop, M i^6 < L i/32:=by
    let c:= G.slopeConstant⁻¹; have hc:0<c:=inv_pos.mpr (Gauge.slopeConstant_pos h)
    filter_upwards [he.eventually (Vac.Numbers.cost 7 1 one_pos), hM.eventually_gt_atTop (64/c),
      (log_hat hq h).eventually (lt_mem_nhds (half_lt_self hc))] with i hi hm hp
    simp only [Real.rpow_one,show (7:ℝ)=↑(7:ℕ) from rfl, Real.rpow_natCast] at hi 
    have hf : M i ^ 7 ≤ m i := by exact hi
    have hJ:c/2 < L i/m i:=hp
    have hL:= (lt_div_iff₀ (Terrace.bell ..)).mp hJ
    have hZ:64 < M i*c:= (div_lt_iff₀ hc).mp hm
    have hu:0<M i:= Real.exp_pos _
    nlinarith only [mul_lt_mul_of_pos_left hZ (pow_pos hu 6),mul_le_mul_of_nonneg_left hf hc.le,hL]
  have hlim:Tendsto (fun i=> J.r i * L i/32) atTop (𝓝 0) := by
    have he(i):Real.exp (-L i)=J.r i:=by rw [Real.exp_neg]; unfold L LogZoom; rw [Real.exp_log (inv_pos.mpr (J.positive i)),inv_inv]
    have h0:= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (Over.a_clock (J:=J))
    have hu:=h0.div_const (32:ℝ)
    simpa only [Function.comp_def,pow_one, L, (show ∀ i, Real.exp (-LogZoom J i)= _ from he), zero_div,mul_comm] using! hu
  filter_upwards [hF,hv,hq.growth.eventually (block_upper (A') h θ), hlim.eventually (gt_mem_nhds (show 0<(1:ℝ) from one_pos)), hM.eventually_ge_atTop 1] with i hi hv hu hs hU
  have hw:w i≠0 := by
    intro he; rw [he,C.S.a_zero] at hv
    have hh: (1:ℝ)<1:= calc
      1 ≤ J.r i * M i^5 := hv
      _ ≤ J.r i * M i^6 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (by decide)) (J.positive i).le
      _ < J.r i * L i / 32 := by rw [mul_div_assoc]; exact mul_lt_mul_of_pos_left hi (J.positive i)
      _ < 1:=hs
    exact lt_irrefl _ hh
  obtain ⟨r,hr⟩:= Nat.exists_eq_succ_of_ne_zero hw
  have hw':w i-1=r:=by omega
  let s:ℝ := (C.S.block r).val
  have hp: (20:ℝ) < s := by
    have hc := θ.cropK r
    unfold ctl at hc
    have hb:20<(C.S.block r).val:= (Nat.lt_of_lt_of_le (by omega) hc)
    have he : (↑(20:ℕ):ℝ) < s := Nat.cast_lt.mpr hb
    simpa using he
  have he:C.S.a r= s*C.S.a (w i):=by
    rw [hr,C.S.a_step]; change _=s*(C.S.a r/s); field_simp [(lt_trans (by norm_num : (0:ℝ)<20) hp).ne']
  have hz:w i ≤ k i:= (widerSky ..).trans (beforeSky ..)
  have hl : s ≤ M i := hu _ (by change r ≤ k i; omega)
  rw [hw',he]
  refine ⟨Nat.pos_of_ne_zero hw,mul_lt_mul_of_pos_right hp (C.S.a_pos _),?_⟩
  calc
    _ ≤ M i*(J.r i * M i^5) := mul_le_mul hl hv (C.S.a_pos _).le (Real.exp_pos _).le
    _ = J.r i*M i^6 := by ring
    _ < _:= by rw [mul_div_assoc]; exact mul_lt_mul_of_pos_left hi (J.positive i)
end YM.GapsContact.Stamps
