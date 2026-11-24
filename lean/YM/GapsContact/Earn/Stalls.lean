import YM.GapsContact.Earn.Beach

/-! # Terminal estates

Global prices up to bounded length one, pay the few large distances in Gram. Need not depend
on either arity of an exterior or unrelated labels for startup-threshold selection. True operator,
not Hilbert tensor compression. Keep derivative allowances with their exact price at paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Ward Spec Table OS OS.Ground OS.Semigroup Word Climb
open Ascent Power Trace.Pilot Trace Trace.Terrace Trace.Over Work.A05
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Classical

lemma oven_alive {D:Hilbert} {a:Axis} (U : OS.Semigroup D a) (x:D) (t:ℝ≥0) (hx:U.E t x=0) : x=0:=by
   let y(k:ℕ):ℝ≥0:= t/2^k; have he(k:ℕ) : U.E (y k) x=0:=by
     induction k with
     | zero => simpa [y] using hx
     | succ k ih=> apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [U.swing,← ContinuousLinearMap.comp_apply, ← U.time, show y (k+1)+y (k+1)=y k from ?_,ih,inner_zero_right]; unfold y; field_simp; ring
   have hw : Tendsto y atTop (𝓝 0):=by
     -- use embedding into real
     apply (tendsto_subtype_rng ..).2
     dsimp only [y]; exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
   have h:= tendsto_nhds_unique_of_eventuallyEq ((U.continuousE x).continuousAt.tendsto.comp hw) tendsto_const_nhds (Eventually.of_forall he)
   rw [U.eZero] at h; exact h

variable {G:Gauge}{L:Register G} {Ξ : Table L}
lemma power_good (H:Ξ.Hierarchy)(d:ℕ)(r s:ℝ) (hr:0<r)(hs:r ≤ s)(h:Good H d r) : Good H d s := by
   obtain ⟨X⟩:= OS.realization H timeAxis
   have hp : 0<s:=hr.trans_le hs
   intro x hx; by_contra! hh; obtain hK:= h x hx
   let F(v)(h:0<v):= X.GNS.plant (sourceWord (Ξ.representative d x) h)
   have heq (v:ℝ) (he:0<v) : chip H d v x= ‖F v he‖:=by
      have hp:= psalm H X he (Ξ.representative d x) (Ξ.representative d x); rw [Ξ.rep] at hp
      unfold chip valTwo; rw [hp,inner_self_eq_norm_sq_to_K]; change Real.sqrt ‖(↑‖F v he‖:ℂ)^2‖=_; rw [← Complex.ofReal_pow,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
   rw [heq s hp] at hh; rw [heq r hr] at hK
   let v:ℝ≥0:=⟨(s-r)/2,div_nonneg (sub_nonneg.mpr hs) zero_le_two⟩
   have hg: sourceWord (Ξ.representative d x) hp= OS.travel (sourceWord (Ξ.representative d x) hr) v:= by
      apply Subtype.ext; unfold OS.travel; simp only [sourceWord, Word.carry,List.map_cons,List.map_nil]; rw [← add_smul]; change _ = [((r/2+(s-r)/2) • basis timeAxis, (⟨d,Ξ.representative d x⟩: L.Token))]; rw [show r/2+(s-r)/2=s/2 by ring]
   unfold F at hh; rw [hg,X.atBirth] at hh; exact (norm_pos_iff.mp hK) (oven_alive X.flow _ v (norm_le_zero_iff.mp hh))

variable {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S) {hG:G.Simple}{A:EveryPhase.Almanac F}
local notation "Q"=>F.sector.derivatives
local notation "Hh" => F.room.kernel
local notation "aQ"=> F.phase.transport.spots
local notation "I"=> Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric
universe u
variable (T:Roll.{u} F hG A)
include T
lemma all_good (t:ℝ)(ht:0<t)(d:ℕ) : Good Hh d t:=by
   obtain ⟨H,W,ℓ,hU,-,-⟩:=T.trace.stress
   obtain ⟨r,⟨hr,hy⟩,hp⟩:= (((stronger F hG hU d).and (show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin)).and ((ge_mem_nhds ht).filter_mono nhdsWithin_le_nhds)).exists
   exact power_good Hh d r t hy hp hr
lemma cash_price (d:ℕ) (r u:ℝ)(hr:0< r)(hu:0<u) : ∃ B:ℝ,1≤B ∧ ∀ x:S.Field d,cost F d r x ≤ B*cost F d u x:=by
   letI : FiniteDimensional ℝ (S.Field d):= Module.Finite.trans ℂ _
   exact metric_paid _ _ (chip_cont Hh d r hr) (chip_cont Hh d u hu) (fun c x=>chip_real Hh _ x c) (fun c x=>chip_real Hh _ x c) (all_good F T u hu d)

/- Useful global for any map Φ independent of length, any index range provided same B. -/
lemma cash_exchange {X:Type*}(d e:ℕ)(F' : X→ S.Field d→S.Field e)(p:ℕ) (h:∃ B:ℝ,1≤ B∧∀ᶠ r in trail,∀ k x,r^p*cost F e r (F' k x) ≤ B*cost F d r x):∃ B:ℝ,1≤B ∧ ∀ r∈Ioc (0:ℝ) 1,∀ k x,r^p*cost F e r (F' k x) ≤ B*cost F d r x:=by
   obtain ⟨B,hB,h⟩:= h; obtain ⟨R,hR,hV⟩:=smallEstate h
   let t:=min 1 R; have ht:0<t:= lt_min one_pos hR
   obtain ⟨D,hD,hY⟩:= cash_price F T d t 1 ht one_pos
   let b:ℝ:= (t^p)⁻¹*(B*D)
   refine ⟨max B b,hB.trans (le_max_left ..),fun r hr k x=> ?_⟩
   by_cases he:r ≤ t; · exact (hV r ⟨hr.1,he.trans (min_le_right ..)⟩ k x).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Ascent.cost_pos ..))
   have hs:t ≤ r:= le_of_not_ge he; have hx: cost F e t (F' k x) ≤ (t^p)⁻¹*(B*cost F d t x):= (le_inv_mul_iff₀ (pow_pos ht _)).2 (hV t ⟨ht,min_le_right ..⟩ k x)
   calc
      _ ≤ cost F e t (F' k x):= (mul_le_of_le_one_left (Ascent.cost_pos ..) (pow_le_one₀ hr.1.le hr.2)).trans (power_signal Hh _ ht hs)
      _ ≤ (t^p)⁻¹*(B*(D*cost F d r x)):= hx.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((hY x).trans (mul_le_mul_of_nonneg_left (power_signal Hh _ hr.1 hr.2) (zero_le_one.trans hD))) (zero_le_one.trans hB)) (by positivity))
      _ ≤ _:=by have hp : (t^p)⁻¹*(B* (D*cost F d r x))= b*cost F d r x:=by unfold b; ring
                rw [hp]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (Ascent.cost_pos ..)
lemma cash_spin (d:ℕ):∃ B:ℝ,1≤B∧∀ r∈Ioc (0:ℝ) 1,∀ x:S.Field d,cost F d r (flipField F d x)≤B*cost F d r x := by
   simpa using! (cash_exchange F T d d (fun _:Unit=> flipField F d) 0 (by simpa using spin_flight F A T d))
lemma cash_derivative (d:ℕ)(a:Axis):∃ B:ℝ,1≤ B ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ x:S.Field d,r*cost F (d+1) r ((Q).deriv d a x)≤ B*cost F d r x:=by
   obtain ⟨C',hc,hV⟩:= starlight F A T d a
   simp_rw [paid_coin,chip_real] at hV
   have hh:= cash_exchange F T d (d+1) (fun _:Unit=> (Q).deriv d a) 1 (by refine ⟨C',hc,?_⟩; filter_upwards [hV,self_mem_nhdsWithin] with r hr ht u x; rw [paid_coin,paid_coin,pow_one]; rw [Real.norm_of_nonneg (mem_Ioi.mp ht).le] at hr; exact hr x)
   simpa using hh

-- With ceiling even at large s. log here increases when going down. Extend Sky estimate to all slots.
def dock (r:ℝ):ℝ:= 8 + LogV r
omit T
lemma dock_valid (r:ℝ)(hr:r∈Ioc (0:ℝ) 1) : 1 ≤ dock r:=by unfold dock LogV; have hh:= Real.log_nonneg ((one_le_inv₀ hr.1).2 hr.2); linarith
lemma dock_fold (x y:ℝ)(hx:0<x)(ht:x≤y) : dock y≤ dock x:=by unfold dock LogV; rw [Real.log_inv,Real.log_inv]; have h:= Real.strictMonoOn_log.monotoneOn hx (hx.trans_le ht) ht; linarith
include T
lemma seaside (d:ℕ)(δ:ℝ)(hd:δ∈ Ioc (0:ℝ) 1) :∃ (B:ℝ)(m:ℕ), 1 ≤ B ∧ ∀ r∈Ioc (0:ℝ) 1,∀ p:ℝ≥0,∀ hp:0<p, r*δ ≤ p →∀ (x:S.Field d)(t:Ortho),
    ‖I hp d (F.sector.turns.act d t x)‖ ≤ B * dock r ^ m * cost F d r x:=by
   obtain ⟨R,A₀,m,hR,hA,hX⟩:= T.slabs d; obtain ⟨B,hB,hv⟩:= tornado F A T d; obtain ⟨l,hl,hY⟩:= smallEstate hv
   let u:= min (min R 1) l; have hu:0<u:= lt_min (lt_min hR one_pos) hl
   obtain ⟨C',hC,hw⟩:= cash_price F T d u 1 hu one_pos
   let D:= A₀^2*(δ⁻¹)^(2*m)*B; have hv:1≤D:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ ((one_le_inv₀ hd.1).2 hd.2))) hB
   have ht(r)(hr:r∈ Ioc 0 u)(p:ℝ≥0)(hp:0<p)(he:r*δ ≤ p)(x:S.Field d)(t:Ortho): ‖I hp d (F.sector.turns.act d t x)‖ ≤ D*dock r^(2*m)*cost F d r x:=by
      have hf:r∈ Ioc 0 R:=⟨hr.1,hr.2.trans ((min_le_left ..).trans (min_le_left ..))⟩
      have hg : 4 ≤ LogV r:= hX.duration r hf
      have hy : LogV r ≤ dock r:=by unfold dock; linarith
      apply (own_pay F hX.archive hA hf hd hg p hp he _).trans; unfold D; rw [show _*B*dock r^(2*m) * cost F d r x=A₀^2*(dock r/δ)^(2*m)*(B*cost F d r x) from ?_]; swap; · rw [div_eq_mul_inv,mul_pow]; ring
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have hh:=hd.1; change 0 ≤ LogV r/δ; positivity) (div_le_div_of_nonneg_right hy hd.1.le) _) (sq_nonneg _)) (hY r ⟨hr.1,hr.2.trans (min_le_right ..)⟩ t x) (Ascent.cost_pos ..) (mul_nonneg (sq_nonneg _) (by unfold dock; rw [pow_mul]; positivity))
   let H:=D*dock u^(2*m)*C'; refine ⟨max D H,2*m,hv.trans (le_max_left ..),fun r hr p hp he x t=>?_⟩
   by_cases hu':r≤u; · exact (ht r ⟨hr.1,hu'⟩ p hp he x t).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by rw[pow_mul]; positivity)) (Ascent.cost_pos ..))
   have hy:u≤r:= le_of_not_ge hu'; apply (ht u ⟨hu,le_rfl⟩ p hp ((mul_le_mul_of_nonneg_right hy hd.1.le).trans he) x t).trans
   calc
     _ ≤ D*dock u^(2*m) * (C' * cost F d r x):= by rw [pow_mul]; gcongr; exact (hw x).trans (mul_le_mul_of_nonneg_left (power_signal Hh _ hr.1 hr.2) (zero_le_one.trans hC))
     _ = H * cost F d r x:= by unfold H; ring
     _ ≤ _:= mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_mul_of_one_le_right (zero_le_one.trans (hv.trans (le_max_left ..))) (one_le_pow₀ (dock_valid r hr)))) (Ascent.cost_pos ..)

-- clipped ratio extends dynastic sharp bounds to all bounded widths. Also keep sales grade.
lemma token_grants (d:ℕ) (ε:ℝ)(he:0<ε) :∃ B:ℝ, Market F d ε 1 B:=by
   obtain ⟨H,Z,ℓ,hU,-,-⟩:=T.trace.stress
   obtain ⟨R',B,hV⟩:= marketplace0 F hG hU d ε he; let R:=min 1 R'; have hR:0<R:= lt_min one_pos hV.road; have hr:R≤1:= min_le_left ..; have hwR:R≤R':= min_le_right ..
   have hx:= hV.refresh F hR hwR le_rfl le_rfl
   obtain ⟨D,hD,h⟩:= cash_price F T d R 1 hR one_pos
   let m:= (d:ℝ)+ε; let k:= (d:ℝ)-ε; let v:=R⁻¹^(d:ℕ)
   have hm: 0 < m:=by unfold m; positivity
   have hv:1≤v:= one_le_pow₀ ((one_le_inv₀ hR).2 hr); have hf: 1≤D*v:= one_le_mul_of_one_le_of_one_le hD hv
   have hB:= hx.budget
   have hD':1≤B*(D*v):= one_le_mul_of_one_le_of_one_le hB hf
   let c:=B* (D*v); have hh:B ≤ c:= le_mul_of_one_le_right (zero_le_one.trans hB) hf; have hc:B*D≤c:=by unfold c; gcongr; exact le_mul_of_one_le_right (zero_le_one.trans hD) hv
   have hY {i:ℝ}(hi:i∈Ioc 0 (1:ℝ))(x:S.Field d):chip Hh d R x ≤ D*chip Hh d i x:= (h x).trans (mul_le_mul_of_nonneg_left (power_signal Hh x hi.1 hi.2) (zero_le_one.trans hD))
   have hz:= hx.refresh F hR le_rfl hh le_rfl
   have hPow {t:ℝ}(ht: 0<t)(hx:t≤1)(hs: R ≤ t) : 1 ≤ v*t^k:=by
      have hu : t^(d:ℕ) ≤ t^k:=by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge ht hx (sub_le_self _ he.le)
      calc (1:ℝ) = v* R^d:=by unfold v; rw [inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hR.ne')]
           _ ≤ v*t^k := mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hR.le hs _).trans hu) (zero_le_one.trans hv)
   refine ⟨c,⟨one_pos,hD',?_,?_,fun s hs=> all_good F T s hs.1 d,?_,?_⟩⟩
   · intro s hs x; rcases le_total s R with hp|hp; · exact hz.uniform_top s ⟨hs.1,hp⟩ x
     simp_rw [paid_coin]
     refine (power_signal Hh _ hR hp).trans (((hx.uniform_top R ⟨hR,le_rfl⟩ x).trans ?_)); exact le_trans (b:=B*(D*chip Hh d s x)) (mul_le_mul_of_nonneg_left (hY hs x) (zero_le_one.trans hB)) ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hc (chip_nn ..)))
   · intro e he s hs x; rcases le_total s R with hp|hp; · exact hz.tier e he s ⟨hs.1,hp⟩ x
     simp_rw [paid_coin]
     refine (power_signal Hh _ hR hp).trans (((hx.tier e he R ⟨hR,le_rfl⟩ x).trans ?_)); exact le_trans (b:=B*(D*chip Hh d s x)) (mul_le_mul_of_nonneg_left (hY hs x) (zero_le_one.trans hB)) ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hc (chip_nn ..)))
   · intro s t hs ht x; rcases le_total s R with hp|hp; · exact hz.left ⟨hs.1,hp⟩ ht x
     have hf:R/t>0:=div_pos hR ht.1; simp_rw [paid_coin]
     have he': (R/t)^m ≤ (s/t)^m:= Real.rpow_le_rpow hf.le (div_le_div_of_nonneg_right hp ht.1.le) hm.le
     rcases le_total t R with ht'|ht'
     · refine le_trans (hx.left ⟨hR,le_rfl⟩ (show t∈ Ioc 0 R from ⟨ht.1,ht'⟩) x) (le_trans (b:= (B * (R/t)^m) * (D * chip Hh d s x)) ?_ ?_)
       · exact mul_le_mul_of_nonneg_left (hY hs x) (by change 0 ≤ B*(R/t)^m; positivity)
       rw [show B*(R/t)^m* (D*chip Hh d s x)= B*D*(R/t)^m * chip Hh d s x from (by ring)]; gcongr; apply chip_nn
     refine le_trans (power_signal Hh x hR ht') ((hY hs x).trans (mul_le_mul_of_nonneg_right ?_ (chip_nn ..))); refine le_trans (b:=B*D) (le_mul_of_one_le_left (zero_le_one.trans hD) hB) (le_trans hc ?_); exact le_mul_of_one_le_right (zero_le_one.trans hD') (Real.one_le_rpow ((one_le_div ht.1).2 ht.2) hm.le)
   intro s t hs ht x hf; simp_rw [paid_coin]; rcases le_total s R with hp|hp; · exact hz.sale ⟨hs.1,hp⟩ ht x hf
   have hD'' : v * B ≤ c:= by unfold c; rw [←mul_assoc, mul_comm v];  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans hB) hD) (zero_le_one.trans hv)
   have hU(t:ℝ)(ht:t ∈ Icc R s): 1 ≤ v*(t/s)^k:=by
       have ht':0<t:= hR.trans_le ht.1; apply hPow (div_pos ht' hs.1) ((div_le_one hs.1).2 ht.2); exact ht.1.trans ((le_div_iff₀ hs.1).2 (mul_le_of_le_one_right ht'.le hs.2))
   rcases le_total t R with h₁|h₁
   swap
   · refine (power_signal Hh x ht.1 ht.2).trans (le_mul_of_one_le_left (chip_nn ..) ((hU t ⟨h₁,ht.2⟩).trans (mul_le_mul_of_nonneg_right (le_trans (le_mul_of_one_le_right (zero_le_one.trans hv) hB) hD'') (Real.rpow_nonneg (div_pos ht.1 hs.1).le _))))
   refine (power_signal Hh x hR hp).trans (le_trans (hx.sale ⟨hR,le_rfl⟩ (show t∈ Ioc 0 R from ⟨ht.1,h₁⟩) x hf) (mul_le_mul_of_nonneg_right ?_ (chip_nn Hh d t x)))
   have ha:t/s=R/s*(t/R):=by have he:=hR.ne'; field_simp
   have hz' := Real.rpow_nonneg (div_pos ht.1 hR|>.le) k; have he':= Real.rpow_nonneg (div_pos hR hs.1|>.le) k
   calc
     _ ≤ B*(t/R)^k* (v*(R/s)^k) := le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hB) hz') (hU R ⟨le_rfl,hp⟩)
     _ = (v*B)*(t/s)^k:= by rw [ha,Real.mul_rpow (div_pos hR hs.1|>.le) (div_pos ht.1 hR|>.le)]; ring
     _ ≤ _:= mul_le_mul_of_nonneg_right hD'' (Real.rpow_nonneg (div_pos ht.1 hs.1).le _)

lemma beach_all {n:ℕ}(d:Fin n→ℕ){μ:ℝ}(hμ:0<μ) :
   ∃ (B:ℝ)(m:ℕ),1≤B ∧ ∀ g∈Ioc (0:ℝ) 1,∀ (x:Points n) (r:Fin n→ℝ), (∀ i,r i∈ Icc g 1) → Pairwise (fun i j=>μ*r i ≤ ‖x i-x j‖) →
     ∀ (s:Survey F) (v:∀ i,S.Field (d i)), ‖S.useAt (Survey.table s) x (fun i=>⟨d i,v i⟩)‖ ≤ B * dock g^m * (∏ i,cost F (d i) (r i) (v i)) :=by
   obtain ⟨a,ha,hE⟩:= OPE.Coverage.directions (Fin n × Fin n); let δ:= min 1 (μ*a/4); have hd:0<δ:= lt_min one_pos (by positivity)
   choose A' m HA HH using fun i=> seaside F T (d i) δ ⟨hd,min_le_left ..⟩
   refine ⟨∏ i,A' i,∑ i, m i,Finset.one_le_prod (fun i _=> HA i), fun g hg x r hG' hA s v=>?_⟩
   have hr(i): r i∈ Ioc (0:ℝ) 1:= ⟨hg.1.trans_le (hG' i).1,(hG' i).2⟩
   let p(i):ℝ≥0:=⟨r i*δ,(mul_pos (hr i).1 hd).le⟩; have hp(i) : 0<p i:=mul_pos (hr i).1 hd
   have hX:F.sector.turns.Oriented (Survey.table s):=by
     cases s with | some i=> exact F.phase.phase.sym i | none=> exact F.phase.transport.motion
   obtain ⟨K,h⟩:= hE (fun i:Fin n×Fin n=> x i.1-x i.2)
   have hu:x∈ conf _:=by intro i j hh; by_contra! hv; have he:= (mul_pos hμ (hr i).1).trans_le (hA hv); rw [hh,sub_self,norm_zero] at he; exact lt_irrefl _ he
   have hf: Pairwise (fun i j=> (p i:ℝ)+(p j:ℝ)< |Ortho.move K (x i) timeAxis-Ortho.move K (x j) timeAxis|):=by
      intro i j hij; dsimp only; have hv:= (hG' i).1; have hq:= (hr j).1; have he:δ≤ μ*a/4:= min_le_right ..
      let R:=‖x i-x j‖; have hi:μ*r i ≤ R:= hA hij; have hj:μ*r j ≤ R:= (hA hij.symm).trans_eq (norm_sub_rev ..); have hs:r i*δ+r j*δ<a*R:=by nlinarith only [hi,hj,he,mul_pos hμ (hr i).1,mul_pos ha (hr i).1,mul_pos ha (mul_pos hμ (hr i).1),ha,(hr i).1,hq]
      refine hs.trans_le ((h (i,j)).trans_eq ?_); change |Ortho.move K (x i-x j) timeAxis| = _; rw [show Ortho.move K (x i-x j)= Ortho.move K (x i)-Ortho.move K (x j) from (Ortho.motion K).map_sub ..]; rfl
   rw [← hX n _ x hu K]; let w(i):= F.sector.turns.act _ K (v i); apply (region F A w _ s p hp hf).trans ?_
   rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]; refine Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=>?_)
   exact (HH i (r i) (hr i) _ (hp i) (le_refl _) (v i) K).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (dock_valid _ (hr i))) (dock_fold g _ hg.1 (hG' i).1) _) (zero_le_one.trans (HA i))) (Ascent.cost_pos ..))
end YM.GapsContact.Seams
