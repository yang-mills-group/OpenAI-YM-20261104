import YM.OPE.Therm.Rite

/-! The full thermal chessboard price on the genuine memento tiles.
The vacuum comparison calculations are those of OPE.Therm.Rarity.away and
OPE.Therm.Rite.rare, stopped before the singleton comparison. The funded
power eleven is kept before summing geometric residue classes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.ReplicaPressure
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Rank Push.GridApprox Cells WardBin.Wheels
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge} {H:History G}(Y:H.Selected){k i m N p:ℕ} {τ g :ℝ}
local notation "n" j => H.S.side j p
local notation "Q" j => H.rep N p j
local notation "η" j => prior G (H.S.side j p)
local notation "ℤ∞" => partition G (H.S.side N p) (H.β N p N)
local notation "μ" j => scene H N p j
local notation "P*" => H.levels
local notation "Ξ" => Vac.treasury H.levels k
local notation "c₀" => H.levels.clock
section spot
variable {v:Side}
local notation "vol0" => (Fintype.card (Site v):ℝ)
local notation "ac" => (Fintype.card PlaqAxes:ℝ)
private lemma local_face {R : Rep G v}{σ A Λ δ w:ℝ}(Y:R.Lawful σ A Λ δ w) (hw:w≤1) (hg :0<g) (he:g ≤ R.p.threshold) (hm:R.beta*g^2=1) (T:Tiling v)(z:Face (Per v))(h:(touched z : Set _) ⊆ T.chamber 0) :
    let e:ℝ:= g / strength R.clip
    let a:= τ/e*Fintype.card T.Cell
    ∀ U, ‖(R.eval U:ℂ)* T.fullAt (fun _=>fires z τ) U‖ ≤ Real.exp (R.scalar+vol0*(R.exCost A Λ δ + ac) - a) :=by
   intro e a U; let r(i:Face (Per v))(U:Config G v):= G.chord (faceValue U i)/e; have hx:=trigger_injective T z h
   let g' (j:T.Cell):= Face.send (T.omega j) (T.translateBy j) z; let R₀:=∑ j,r j U
   have hh (j): T.copy j (fires z τ) U = fires (g' j) τ U:= congr_fun (fire_copy T z τ j) U
   unfold Tiling.fullAt; simp_rw [hh]; by_cases hy : ∀ j:T.Cell,U ∈ trigger (g' j) τ; swap
   · push Not at hy; obtain ⟨j,hj⟩:=hy
     rw [Finset.prod_eq_zero (Finset.mem_univ j) (f:=fun j=> fires (g' j) τ U) ?zero]; simp [(Real.exp_pos _).le] -- b not arg
     case zero=> exact indicator_of_notMem hj 1
   have hE : 0<e:= div_pos hg (strength_pos _); have hr(i):0 ≤ r i U:=div_nonneg (G.chord_nonneg _) hE.le
   have hT : a ≤ R₀:=by
      have ht:=Finset.sum_le_sum_of_subset_of_nonneg (f:=fun i=>r i U) (Finset.subset_univ (Finset.univ.image g')) (by intros; apply hr)
      rw [Finset.sum_image hx.injOn] at ht; apply le_trans ?_ ht
      unfold a; rw [mul_comm _ ((Fintype.card T.Cell):ℝ), ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i _=> div_le_div_of_nonneg_right (show τ ≤ _ from le_of_lt (hy i)) hE.le
   have hv (i): fires (g' i) τ U=1:= indicator_of_mem (hy i) 1; simp_rw [hv]; simp only [Finset.prod_const_one,mul_one,Rep.eval,Complex.norm_real,norm_mul]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact ((mul_le_mul_of_nonneg_left (SectorNext.Vacuum.gas_le_one R.activities hw Y.labels U) (Real.exp_pos _).le).trans_eq (mul_one _)).trans (Real.exp_monotone (le_trans (exponent_retains Y hg he hm U) (sub_le_sub_left hT _))) -- eq trans_eq type
end spot

include Y
set_option maxHeartbeats 200000 in
theorem full (h : i≤k) (he : k≤N) (t : Face (Per (n k)))
    (hc : (touched t : Set _) ⊆ (tilesAt H.S p h).chamber 0) (hg : 0<g)
    (hγ : g≤(Q k).p.threshold) (hw : (Q k).beta*g^2=1) :
    let a := ((H.S.toDepth h p).count.val : ℝ)^4
    let b := strength ((P*).params k).clip
    ‖∫ U,(tilesAt H.S p h).fullAt (fun _ => fires t τ) U ∂(μ k)‖ ≤
      (Real.exp (a*(Ξ+Fintype.card PlaqAxes)-τ/(g/b)))^(Fintype.card (tilesAt H.S p h).Cell) := by
    let c:=H.levels.clock
    let U:=H.levels.params k
    intro a b
    let R:=H.rep N p k
    let P:=tilesAt H.S p h
    let C':ℝ:=Fintype.card P.Cell; let W:ℝ:=Fintype.card (Site (n k)); let L:=c.loopCap k; let A:=U.paths; let X:= c.hatCoupling k; let V:=c.allowance k; let WQ:=c.forcedAllowance k; let B:= Fintype.card PlaqAxes; let σ:= R.exCost A L V
    let b1:= R.scalar-W*(σ+R.beta*baseBudget R.clip A X)-(Fintype.card (Edge (Site (n k))):ℝ)*Module.finrank ℝ G.Mat* Real.log (16/X)
    let b2:=R.scalar+ W*(σ+B) - τ/(g/b)*C'; let a0:= a*(Ξ+B) - τ/(g/b)
    have hR:= Y.represents N p k he; have hvac:=hR.vac
    have hn :0<X:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((P*).fits.delayed _)))
    have hE:X≤ R.p.threshold:= by
       change X≤(Q k).p.threshold; rw [hvac]
       exact le_mul_of_one_le_right hn.le (Real.one_le_exp (sq_nonneg _))
    have hz : 0<R.beta := by
       refine lt_of_lt_of_le ?_ hR.band.1; have h:= (P*).fits.delayed k; linarith only [h]
    have hK : 0<WQ := Real.exp_pos _
    have hΨ : WQ ≤ 1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
    let F:=fires (G:=G) t τ
    letI:= probability (p:=p) Y he
    have hV := Vac.suffices_bill (H:=H) (p:=p) Y he 0 0 0 0 0
    simp only [Overlay.Bands.finalBill, Nat.cast_zero,zero_mul,add_zero] at hV; change W*(2*σ+WQ+ R.beta*baseBudget R.clip A X+4*Module.finrank ℝ G.Mat*Real.log (16/X)) ≤ W*Ξ at hV -- clip
    have hZ : W=C'*a:=by
       unfold W C' a; change (↑(Fintype.card (Site (n k))) : ℝ)= ↑(Fintype.card (Site (n i)))*_; simp_rw [site_card]; rw [(H.S.toDepth h p).exact_size]; push_cast; ring
    have h₀:0≤W:=Nat.cast_nonneg _
    rw [violet Y he,norm_div,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le, div_le_iff₀ (partition_pos _)]
    have hD : Real.exp b1 ≤ ℤ∞:= by
       rw [← H.partition_eq Y N p k he]; exact R.denominator hR.good hz.le X hn hE (fun u=> (gravity Y he u).le)
    let Y'(U:Config G (n k)):=((Q k).eval U:ℂ)* P.fullAt (fun _=> F) U
    have hA(U): ‖Y' U‖ ≤ Real.exp b2:=by
       have htz: strength ((Q k).clip) = b := congr_arg _ hR.clip
       have ht:=local_face (τ:=τ) hR.good hΨ hg hγ hw P t hc U; rw [htz] at ht; exact ht
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hD (pow_nonneg (Real.exp_pos _).le _)); rw [← Real.exp_nat_mul,← Real.exp_add]
    have hb : ‖∫ U,Y' U∂(η k)‖ ≤ Real.exp b2:= by simpa using norm_integral_le_of_norm_le_const («μ»:=η k) (Eventually.of_forall hA)
    apply hb.trans (Real.exp_monotone ?_); change b2 ≤ C'*a0+b1
    have hh : (Fintype.card (Edge (Site (n k))):ℝ)=4*W:= by unfold W; simp [Edge,Axis,mul_comm]
    unfold b1 b2 a0; rw [hh]; have he' :=mul_nonneg h₀ hK.le; rw [hZ] at he' hV ⊢; linarith
end YM.OPE.Therm.ReplicaPressure
end

noncomputable section
namespace YM.OPE.Therm.ReplicaPressure
open Function Filter Set MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock Push.PriceCompiler Next.Foundations
open scoped ENNReal Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {H:History G}{i N p:ℕ}
local notation "U" => H.levels
variable (Y:Poetry H.levels)(θ:G.Simple)
local notation "X" => H.levels.clock.hatBeta
local notation "L" => sigmaU H.levels
local notation "K" => H.S
local notation "s" => H.S.a
local notation "d" => H.levels.clock.J
local notation "ℓ" => H.levels.clock.hatCoupling
local notation "τ" => cool H.levels
local notation "e" => vanishP H.levels
include θ
include Y
theorem mesh : ∀ᶠ i:ℕ in atTop, ∃ (k:ℕ)(h:k ≤ i), room U k i 2 ∧ ∀ p:ℕ, ((H.S.toDepth h p).count.val:ℝ) ≤ L i^2 := by
    filter_upwards [(log_raised («K»:=U) θ).eventually_gt_atTop 1,(ember_mul («K»:=U) θ 1).eventually (gt_mem_nhds zero_lt_one)] with i hi h
    have hh : L i ≤ X i:= Real.log_le_self (zero_le_one.trans ((U).fits.delayed _).le)
    have hp:s i*X i<1:= by simpa only [mem_Iio,pow_one] using h
    obtain ⟨k,hk,ht,hK⟩:= shelter («K»:=U) i (L i) hi (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh (H.S.a_pos _).le) hp)
    have hf:(d i:ℝ)≥0:= Nat.cast_nonneg _
    have hz:= (Y.stage i).pedestal
    refine ⟨k,hk.le,lt_of_lt_of_le ?_ hK.le,fun p=>?_⟩
    · unfold tail; change 2*(_* ((2:ℕ):ℝ)+_) < _; push_cast; change 100000*((d i:ℝ)+1) ≤ L i at hz; have hh:= H.S.a_pos i
      nlinarith only [mul_le_mul_of_nonneg_right hz hh.le,mul_nonneg hh.le hf, hh]
    have hc:= H.S.embeds_scale (H.S.toDepth hk.le p)
    let a:ℝ := (H.S.block k).val; have ha:0<a:= by unfold a; exact_mod_cast (H.S.block k).pos
    have hM:a ≤ L i := (Y.stage k).track.trans (Real.log_le_log (zero_lt_one.trans ((U).fits.delayed _)) (WilsonStartup.Timing.hat_mono U (Gauge.slopeConstant_pos θ).le hk.le))
    apply le_of_mul_le_mul_left (a:=s i) _ (H.S.a_pos i); rw [hc]; calc
       _ = a*s (k+1):=by rw [H.S.a_step,mul_div_cancel₀ _ ha.ne']
       _ ≤ L i*(L i*s i):= mul_le_mul hM ht (H.S.a_pos _).le (zero_le_one.trans hi.le)
       _ = _:=by ring

/-- The tiling and its room are chosen before every regulator, period, plaquette
and array size. Each true thermal full root has the original order-eleven price. -/
theorem purchased (Z : H.Selected) : ∀ᶠ k : ℕ in atTop,∃(i:ℕ)(hk:i≤k),room U i k 2 ∧
    (∀p : ℕ,((H.S.toDepth hk p).count.val:ℝ) ≤ (L k)^2) ∧
    ∀N,k≤N → ∀(p : ℕ) (t : Face (Per (H.S.side k p))),
    (touched t : Set _) ⊆ (tilesAt H.S p hk).chamber 0 →
    ‖∫ W,(tilesAt H.S p hk).fullAt (fun _=>fires t (τ k)) W ∂scene H N p k‖ ≤
      (Real.exp (-4*(L k)^11))^(Fintype.card (tilesAt H.S p hk).Cell) := by
  filter_upwards [mesh Y θ,Vac.treasury_stage U θ,(log_raised («K»:=U) θ).eventually_gt_atTop 100,
    narrow (H:=H) θ] with k ⟨i,hk,hroom,hi⟩ hv hh hτ
  refine ⟨i,hk,hroom,hi,?_⟩
  intro N hN p t htile
  let b:= X k; let g := ℓ k; let l:= L k; let R:= H.rep N p k; let g' := gap R.beta; have he:=Z.represents N p k hN; have hb : 1<b:= (U).fits.delayed _
  have hβ : 0 < R.beta:= by refine lt_of_lt_of_le ?_ he.band.1; linarith only [hb]
  have hg' : 0<g':= inv_pos.mpr (Real.sqrt_pos.mpr hβ); have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hb)); have hδ : g' ≤ 2*g:= (band_gap b _ (zero_lt_one.trans hb) (trial_in he.band)).2
  have h1: 1≤ l:= (show (1:ℝ)≤100 by norm_num).trans hh.le
  have hν: R.beta * g'^2=1 := by unfold g' gap; field_simp; exact (Real.sq_sqrt hβ.le).symm
  have hw:g'≤R.p.threshold:=by
     apply hδ.trans; unfold R; rw [he.vac]; apply le_trans ?_ hτ.2; unfold cool; change 2*g ≤ 4*(g*l^12); nlinarith only [one_le_pow₀ (n:=12) h1,hg]

  apply (full (p:=p) («τ»:=cool H.levels k) Z hk hN t htile hg' hw hν).trans
  apply pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_monotone ?_)
  let Q:ℝ := (H.S.toDepth hk p).count.val; let a:= Vac.treasury U k + Fintype.card PlaqAxes; let c:= strength ((U).params k).clip
  have hx : a ≤ l^2:= (add_le_add_left hv _).trans ((Y.stage k).price)
  have hA : Q^4*a ≤ l^10:= ((mul_le_mul_of_nonneg_left hx (pow_nonneg (by change 0≤Q; unfold Q; positivity) _)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by change 0≤Q; unfold Q; positivity) (hi p) 4) (sq_nonneg _))).trans_eq (by ring)
  have hz: 100 ≤ l:=hh.le; have hC:0<c:=strength_pos _; have hu:10 ≤ c*l:=by
     rcases le_total 1 ((U).params k).clip.linear with h|h
     · rw [show c=1 from min_eq_left h,one_mul]; exact (show (10:ℝ)≤100 by norm_num).trans hz
     rw [show c=_ from min_eq_right h]; have hv:= (div_le_iff₀ ((U).params k).clip.tail_pos).1 (Y.stage k).strain; simpa only [l,sigmaU,mul_comm] using hv
  have he : 5*l^11 ≤ τ k / (g'/c):=by
     unfold cool; rw [div_div_eq_mul_div, le_div_iff₀ hg']; apply le_trans (mul_le_mul_of_nonneg_left hδ ?_) ?_
     · exact (by have hl:=zero_le_one.trans h1; positivity)
     change 5*l^11*(2*g)≤ g*l^12*c; have hv:= mul_le_mul_of_nonneg_left hu (show 0 ≤ g*l^11 from mul_nonneg hg.le (pow_nonneg (zero_le_one.trans h1) _)); linarith only [hv]
  change Q^4*a-_≤ _; nlinarith only [hA,he, pow_le_pow_right₀ h1 (by norm_num : 10 ≤ 11),sq_nonneg l]
end YM.OPE.Therm.ReplicaPressure
end
