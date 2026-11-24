import YM.RG12SharpGram.Weak.Clock
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.OPE.Height

/-!
# Log-distance plateau lemma

The proof of `MergeProof.East.sponsored` uses a cofinal supply of Poised
stations for weak estimates. We will need the cost of reaching one for
*arbitrary* capture indices. Here is the scheduling part.

The required preceding window for each Poised estimate is length ≤ the log
base L of `hatBeta`, times a power exponent tending to 0, on raising finitely many `readyHere` entries per stage
(this is NOT a price for multiplying transfer norms along the whole schedule!).
This length grows by at most one per step within a plateau. Buy not only this
window but also the timing requirements of the next stage already on the
previous plateau. Thus there's a ready station within this many steps, even
across transitions. No alteration of period or cutoff filters is involved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft.RG12
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis West Pump
open Extra.Iteration.Scales
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}

section cost

def dialPower (j:ℕ) : ℝ := ((j:ℝ)+1)⁻¹
private lemma dp_small (j:ℕ) : 0<dialPower j ∧ dialPower j ≤ 1:=by
  unfold dialPower
  exact ⟨by positivity,inv_le_one_of_one_le₀ (by simp)⟩

abbrev dial (Z : Bar T) (j : ℕ) (s : ℝ) := Station.want (w.L j).val ((Ship.preHat Z s) ^ dialPower j)

private lemma headway (h:G.Simple): Filter.Tendsto (Ship.preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos h))

private lemma factor_large (j:ℕ): 1 < ((w.L j).val:ℝ) := by
  have ht:3 ≤ (w.L j).val:=(w.large j).size
  exact_mod_cast (by omega: 1 < (w.L j).val)

private lemma want_upper (x y:ℝ)(hx:1<x)(hy:1≤y): x^want x y ≤ y*x := by
  cases h:want x y with
  | zero => rw [pow_zero]; exact one_le_mul_of_one_le_of_one_le hy hx.le
  | succ i =>
    have he:x^i < y:= lt_of_not_ge fun hv=> by
      have hh:= (Station.wanted hx (zero_lt_one.trans_le hy) i).1 hv
      omega
    rw [pow_succ]; gcongr

lemma dial_reserve (h:G.Simple)(j:ℕ)(b:ℝ)(hb:0≤b):
    ∀ᶠ s : ℝ in atTop, Ship.benchCost Z b j s ≤ dial Z j s := by
  let P := YM.Vac.Numbers.P
  let x:ℝ:= (w.L j).val
  have hx:1<x := factor_large j; have hx':0<x:=zero_lt_one.trans hx
  have hu: Tiny id (fun z:ℝ=>P z ^ b * P z ^ 2 * x * ((1+(radiusB z:ℝ)) ^ (10:ℕ) * x)) := by
    have hw(p:ℝ): Tiny id (fun z:ℝ=> P z ^ p) := fun ε h => (YM.Vac.Numbers.cost p ε h).mono fun z hz=>⟨Real.rpow_nonneg (Real.exp_pos _).le p,hz⟩
    have hv: Tiny id (fun z:ℝ=> P z ^ (2:ℕ)) := by simpa using hw 2
    have he : Tiny id (fun _:ℝ=>x):= Tiny.const tendsto_id x hx'.le
    exact (((hw b).mul hv tendsto_id).mul he tendsto_id).mul ((Tiny.cover_size.pow tendsto_id 10).mul he tendsto_id) tendsto_id
  refine (headway (Z:=Z) h).eventually (p:=fun z=> Station.bump x b z + Station.more x z ≤ Station.want x (z ^ dialPower j)) ?_
  -- simpler show in `preHat Z s`
  show ∀ᶠ z:ℝ in atTop, Station.bump x b z + Station.more x z ≤ Station.want x (z ^ dialPower j)
  filter_upwards [hu _ (dp_small j).1,eventually_gt_atTop (1:ℝ)] with z hz ht
  let y:=radiusB z
  have hv:1 ≤ P z:=Real.one_le_exp (sq_nonneg _); have hB:1 ≤ P z ^ b* P z^ (2:ℕ):= one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hv hb) (one_le_pow₀ hv)
  have hy:1 ≤ (y:ℝ):= by exact_mod_cast (Nat.ceil_pos.mpr (sq_pos_of_pos (Real.log_pos ht)))
  apply Nat.le_of_not_gt; intro hf
  have hT : x^(Station.want x (z ^ dialPower j)) < x^(Station.bump x b z + Station.more x z) := pow_lt_pow_right₀ hx hf
  refine hT.not_ge ?_
  calc
    _ = x^(Station.bump x b z)*x^(Station.more x z):= pow_add ..
    _ ≤ (P z^b * P z^ (2:ℕ)*x)*((y:ℝ)^(10:ℕ)*x):= mul_le_mul (want_upper x _ hx hB) (want_upper x _ hx (one_le_pow₀ hy)) (pow_nonneg hx'.le _) (mul_nonneg (zero_le_one.trans hB) hx'.le)
    _ ≤ (P z^b * P z^ (2:ℕ)*x)*((1+(y:ℝ))^(10:ℕ)*x):= by gcongr; first| positivity | simp
    _ ≤ z^dialPower j := hz.2
    _ ≤ x ^ want x (z ^ dialPower j) := (Station.wanted hx (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _) _).2 le_rfl

lemma dial_sub (h:G.Simple)(j:ℕ): Tendsto (fun s:ℝ=> (dial Z j s:ℝ)/s) atTop (𝓝 0) := by
  let Q := Ship.preHat Z; let g:= G.slopeConstant
  have ht:= headway (Z:=Z) h; let u:= Real.log ((w.L j).val:ℝ); have hu:0<u:= Real.log_pos (factor_large ..)
  have he : Tendsto (fun s:ℝ=> Q s / s) atTop (𝓝 g) := by
    have hv := ((tendsto_const_nhds (x:=Z.value)).div_atTop (l:=(atTop:Filter ℝ)) tendsto_id).add_const g; rw [zero_add] at hv
    refine hv.congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs; dsimp only [Q,Ship.preHat,g]; simp [add_div,ne_of_gt hs]
  have hv : Tendsto (fun s:ℝ=> Real.log (Q s)/s) atTop (𝓝 0):=by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).mul he; rw [zero_mul] at hh
    refine hh.congr' ?_; filter_upwards [ht.eventually_gt_atTop 0] with s hs
    change Real.log (Q s) / Q s * (Q s / s)=_; rw [div_mul_div_cancel₀ (ne_of_gt hs)]
  have hy : Tendsto (fun s:ℝ=> (Real.log (Q s)/u+1)/s) atTop (𝓝 0):=by
    have hh := (hv.div_const u).add (tendsto_const_nhds (x:=1)|>.div_atTop tendsto_id); rw [zero_div,zero_add] at hh; refine hh.congr (fun s=>?_); change _ + 1/s = _; ring
  refine squeeze_zero' ?_ ?_ hy
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs; exact div_nonneg (by positivity) hs
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually_gt_atTop 1] with s hs ht'
  have hr : dial Z j s ≤ want (w.L j).val (Q s) := by
    apply (Station.wanted (factor_large _) (Real.rpow_pos_of_pos (zero_lt_one.trans ht') (dialPower j)) _).1
    apply le_trans (Real.rpow_le_self_of_one_le ht'.le (dp_small j).2)
    exact (Station.wanted (factor_large _) (zero_lt_one.trans ht') _).2 le_rfl
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hr : (dial Z j s:ℝ)≤ want (w.L j).val (Q s)) hs.le).trans (div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg ht'.le) hu.le)).le hs.le)
end cost

section stage
variable (Z)
-- `R` may incorporate other demands
structure EnoughR (R:ℕ→ℝ) : Prop where
  cap : ∀ j r, R j ≤ r → ((w.L j).val:ℝ) ≤ (Ship.preHat Z r) ^ dialPower j
  slope : ∀ j r, R j ≤ r → Ship.preHat Z r + G.slopeConstant * Real.log (w.L j).val ≤ Ship.preHat Z r * ((w.L j).val:ℝ)

lemma raiseR (R:ℕ→ℝ)(h:G.Simple): ∃ R' : ℕ→ℝ, R ≤ R' ∧ EnoughR Z R':=by
  have ht:= headway (Z:=Z) h
  have he(j:ℕ): let y:ℝ:= ((w.L j).val:ℝ); ∀ᶠ r : ℝ in atTop, (y ≤ (Ship.preHat Z r)^dialPower j ∧ Ship.preHat Z r + G.slopeConstant * Real.log y ≤ Ship.preHat Z r * y):=by
    intro y; have hy:1<y:= factor_large j
    filter_upwards [((tendsto_rpow_atTop (dp_small j).1).comp ht).eventually_ge_atTop y,ht.eventually_ge_atTop (G.slopeConstant * Real.log y / (y-1))] with r hR hr
    exact ⟨hR,by linarith only [(div_le_iff₀ (by linarith only [hy] : 0<y-1)).1 hr]⟩
  choose u hu using fun j:ℕ=> eventually_atTop.mp (he j)
  exact ⟨R⊔u, le_sup_left, fun j r hj=> (hu j r ((le_max_right ..).trans hj)).1, fun j r hj=> (hu j r ((le_max_right ..).trans hj)).2⟩

variable {Z}
variable (R:ℕ→ℝ)(W:Wait Z) {A:Levels G}
private def hold (h:G.Simple): Wait Z :=
  { W with
    readyHere:= fun j=>max (W.readyHere j) (max (R j) (R (j+1)))
    window:= fun j s=> W.window j s+dial Z j s
    sublin := fun j=> by
      simpa only [Nat.cast_add,add_div,add_zero] using (W.sublin j).add (dial_sub (Z:=Z) h j) }

structure Indexed (Z:Bar T) (R:ℕ→ℝ)(A:Levels G) (i:ℕ) : Prop where
  ready : R (A.clock.J i) ≤ A.S.scale i
  bench : dial Z (A.clock.J i) (A.S.scale i) ≤ i
  pad : ∀ m : ℕ, i-dial Z (A.clock.J i) (A.S.scale i) ≤ m → m ≤ i → A.clock.J m= A.clock.J i
set_option quotPrecheck false
local notation "J" => A.clock.J
local notation "S" => A.S
local notation "λ'" => A.S.scale
variable (he:EnoughR Z R)(h:G.Simple)(hp:Paid (hold R W h) A)
include hp

private lemma here_eq (i:ℕ): Ship.preHat Z (λ' i) = A.clock.hatBeta i:=by
  rw [Ship.preHat,Calendar.hatBeta,hp.bar]
private lemma block_wheel (i:ℕ): A.S.block i = w.L (J (i+1)) := (A.fits.sameFactor i).symm.trans (congr_fun hp.lengths _)

private lemma previous_extent (n i k:ℕ)(hi:i≤k)(hb:∀ j, i<j→ j≤k→ J j=n): A.S.a i / A.S.a k = ((w.L n).val:ℝ)^(k-i) := by
  induction k,hi using Nat.le_induction with
  | base => rw [div_self (A.S.a_pos _).ne',Nat.sub_self,pow_zero]
  | succ k hk ih =>
    rw [A.S.a_step,block_wheel R W h hp,hb _ (by omega) le_rfl,show k+1-i=k-i+1 by omega,pow_succ,
      ← ih (fun j hi hj=>hb j hi (by omega))]; field_simp

include he
private lemma inside {i k:ℕ}(hi:Indexed Z R A i)(hs:i≤k)(hj:J k = J i) : Indexed Z R A k := by
  induction k,hs using Nat.le_induction with
  | base => exact hi
  | succ k hk ih =>
    have ht:J k=J i := le_antisymm ((A.fits.mono k.le_succ).trans_eq hj) (A.fits.mono hk)
    have hI:=ih ht
    let j:= J k; let u:ℝ:=(w.L j).val
    have hu:1<u:= factor_large ..
    have hp':J (k+1)=j := hj.trans ht.symm
    have hu' : (λ' (k+1)) = (λ' k) + Real.log u := by
      rw [Schedule.scale_succ,block_wheel R W h hp,hp']
    let B:= dial Z j (λ' k)
    have hZ:k-B ≤ k := Nat.sub_le _ _
    let B':=dial Z (J (k+1)) (λ' (k+1))
    have hB: B' ≤ B+1 := by
      have hv:0<Ship.preHat Z (λ' k):= by rw [here_eq R W h hp]; exact zero_lt_one.trans (A.fits.delayed k)
      unfold B'; rw [hp']; apply (wanted (t:=(Ship.preHat Z (λ' (k+1)))^dialPower j) hu ?pos (B+1)).mp
      case pos => rw [here_eq R W h hp]; exact Real.rpow_pos_of_pos (zero_lt_one.trans (A.fits.delayed (k+1))) _
      have hz : Ship.preHat Z (λ' k)^ dialPower j ≤ u ^ B := (wanted hu
        (Real.rpow_pos_of_pos hv (dialPower j)) B).2 le_rfl
      rw [pow_succ]; apply le_trans (_ : _ ≤ Ship.preHat Z (λ' k) ^ dialPower j *u) (mul_le_mul_of_nonneg_right hz (by linarith only [hu]))
      have hh : Ship.preHat Z (λ' (k+1))= Ship.preHat Z (λ' k)+G.slopeConstant * Real.log u := by
        rw [hu']; unfold Ship.preHat; ring
      have ht:= Real.rpow_le_rpow (show 0 ≤ Ship.preHat Z (λ' (k+1)) by rw [here_eq R W h hp]; exact zero_le_one.trans (A.fits.delayed _).le) (hh.trans_le (he.slope _ _ hI.ready)) (dp_small j).1.le
      rw [Real.mul_rpow hv.le (show 0 ≤ u by linarith only [hu])] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hu.le (dp_small j).2) (by positivity))
    refine ⟨by
      rw [hp']; exact hI.ready.trans ((OPE.scale_mono (S)).monotone k.le_succ),
      hB.trans (Nat.add_le_add_right hI.bench _),?_⟩
    intro m hm hk'; rcases lt_or_eq_of_le hk' with hl|rfl; swap; · exact rfl
    apply (hI.pad m ?_ (by omega)).trans hp'.symm
    change k+1-B' ≤ m at hm; change k-B ≤ m; omega

-- Quantified so arbitrarily many fixed requests inherit the comparison gate.
private lemma directs (N:ℕ): ∀ᶠ k in atTop,
    ∃ m:ℕ,N ≤ m ∧ X.first < J m ∧ Indexed Z R A m ∧ m≤k ∧
      A.S.a m / A.S.a k ≤ A.clock.hatBeta k^(2*dialPower (A.clock.J k)) := by
  filter_upwards [A.fits.deep.eventually_gt_atTop (J N+1), A.fits.deep.eventually_gt_atTop (X.first+1)] with k hk hq
  by_cases ht: Indexed Z R A k
  · have ha : 1 ≤ A.clock.hatBeta k:= (A.fits.delayed k).le
    refine ⟨k,Nat.le_of_not_gt (fun hv=> ?_),by omega,ht,le_rfl,?_⟩
    · have hu:=A.fits.mono hv.le; omega
    rw [div_self (A.S.a_pos k).ne']; exact Real.one_le_rpow ha (by unfold dialPower; positivity)
  let n:= J k-1
  have hn:X.first<n:=by dsimp [n]; omega
  have hz:J k=n+1:=by dsimp [n]; omega
  -- last level of stage n exists below k
  obtain ⟨i,hT,hB,hI⟩:= hp.run n hn.le
  have hj:J i=n:= hI i (Nat.sub_le ..) (by omega)
  have hi:i < k:= lt_of_not_ge fun hu=> by have he:=A.fits.mono hu; omega
  obtain ⟨m,hm,hM⟩:∃ m:ℕ,(m < k ∧ i ≤ m ∧ J m=n) ∧ ∀ m':ℕ,m'<k→ i ≤ m' → J m'=n → m' ≤ m := by
    let v:= (Finset.range k).filter (fun y=> i≤y ∧ J y=n)
    have he(y:ℕ): y∈v↔(y<k ∧ i≤y ∧ J y=n):=by simp only [v,Finset.mem_filter,Finset.mem_range]
    have hv : v.Nonempty :=⟨i,(he i).mpr ⟨hi,le_rfl,hj⟩⟩
    exact ⟨v.max' hv,(he _).mp (Finset.max'_mem ..),fun y hy hi hJ=> Finset.le_max' v y ((he y).mpr ⟨hy,hi,hJ⟩)⟩
  have hh: ∀ y,m<y → y≤k → J y=J k:=by
    intro y hy hv; have hu:= A.fits.mono hv; have hY:=A.fits.mono hy.le
    rcases hm with ⟨hm,hp'',hb⟩
    by_contra hx; have ha:J y=n:=by omega
    have hx':y≠k:=by intro H; subst y; omega
    have hw:= hM y (by omega) (by omega) ha; omega
  have hG' : R (J k) ≤ λ' k:=by
    rw [hz]; apply le_trans _ ((OPE.scale_mono (S)).monotone hi.le)
    exact ((le_max_right ..).trans (le_max_right ..)).trans hT
  have hx':Indexed Z R A i:=by
    have he: dial Z n (λ' i) ≤ (hold R W h).window n (λ' i) := Nat.le_add_left ..
    constructor
    · rw [hj]; exact ((le_max_left ..).trans (le_max_right ..)).trans hT
    · rw [hj]; exact he.trans hB
    · intro l hL hl; rw [hj] at hL; exact (hI l ((Nat.sub_le_sub_left he i).trans hL) (by omega)).trans hj.symm
  let p:=dial Z (J k) (λ' k)
  have hm1:m ≤ k:=hm.1.le
  have hcost:k-m≤p:= Nat.le_of_not_gt (fun he => ht
    { ready:=hG'
      bench:=he.le.trans (Nat.sub_le ..)
      pad:=fun y hy hv=>hh _ (by change k-p ≤ y at hy; omega) hv })
  have hv:N ≤ m:= Nat.le_of_not_gt (fun hu=>by have he:=A.fits.mono hu.le; have hd:J m=n:=hm.2.2; omega)
  refine ⟨m,hv,hm.2.2.symm ▸ hn,inside R W he h hp hx' hm.2.1 (hm.2.2.trans hj.symm),hm1,?_⟩
  rw [previous_extent R W h hp (J k) m k hm1 hh]
  let u:ℝ:=(w.L (J k)).val; let β:=A.clock.hatBeta k
  have ht':1<u:= factor_large ..; have hA:1 < β:=A.fits.delayed k
  change u^(k-m) ≤ β^(2*dialPower (J k))
  have hu' : 1 ≤ β ^ dialPower (J k):= Real.one_le_rpow hA.le (dp_small _).1.le
  rw [two_mul,Real.rpow_add (zero_lt_one.trans hA)]
  refine (pow_le_pow_right₀ ht'.le hcost).trans ((?_ : u^p ≤ β^(dialPower (J k))*u).trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hu')))
  · unfold p dial; rw [here_eq R W h hp k]; exact want_upper u _ ht' hu'
  unfold β; rw [←here_eq R W h hp k]; exact he.cap _ _ hG'

private lemma wheel_short : ∀ᶠ k:ℕ in atTop, ((A.S.block k).val : ℝ) ≤ A.clock.hatBeta k ^ dialPower (A.clock.J (k+1)) := by
  filter_upwards [A.fits.deep.eventually_gt_atTop X.first] with k hk
  let j := J (k+1)-1
  have hz:X.first < J (k+1) := hk.trans_le (A.fits.mono k.le_succ)
  have hq: j+1=J (k+1):=by unfold j; omega
  obtain ⟨i,hT,hB,hI⟩:= hp.run j (by omega)
  have hj:J i=j:= hI i (Nat.sub_le ..) (by omega)
  have hi:i ≤ k := Nat.le_of_not_gt fun hu=> by
    have he:= A.fits.mono (show k+1 ≤ i from hu)
    omega
  have hr:R (J (k+1)) ≤ λ' k:=by
    rw [← hq]; apply le_trans _ ((OPE.scale_mono (S)).monotone hi)
    exact ((le_max_right ..).trans (le_max_right ..)).trans hT
  rw [block_wheel R W h hp,← here_eq R W h hp]
  exact he.cap _ _ hr
end stage

section issue
variable {P:ℕ→ℝ} (W:Wait Z)
-- public supply
lemma stops (he:EnoughR Z P)(h:G.Simple):
    ∃ W':Wait Z, W.minLength ≤ W'.minLength ∧ W.readyHere ≤ W'.readyHere ∧ W.window ≤ W'.window ∧
      ∀ A:Levels G,Paid W' A→(∀ᶠ k:ℕ in atTop, ((A.S.block k).val : ℝ) ≤ A.clock.hatBeta k ^ dialPower (A.clock.J (k+1))) ∧ ∀ N:ℕ, ∀ᶠ k in atTop, ∃ i:ℕ,N ≤ i ∧ X.first < A.clock.J i ∧ Indexed Z P A i ∧ i ≤ k ∧ A.S.a i/A.S.a k ≤ A.clock.hatBeta k^(2*dialPower (A.clock.J k)) :=
    ⟨hold P W h,le_rfl,fun _=>le_max_left ..,fun _ _=> Nat.le_add_right ..,
        fun _ hp=> ⟨wheel_short P W he h hp,directs P W he h hp⟩⟩
end issue
end YM.PhysicalNext.InteractingRank.Soft.RG12
