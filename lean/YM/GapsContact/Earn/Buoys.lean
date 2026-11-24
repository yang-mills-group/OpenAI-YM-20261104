import YM.GapsContact.Earn.Stalls
import YM.OPE.Levy.Invoice

/-!
# Effective source & listener receipts, every actual measuring scale eventual

Not an envelope in a varying exponential washed-out meter. Pay through same ReadLabel
sublimit and the construction owns it (log-price bound at true selected moment stencil).
Multiplicative price in log length, sufficient to permit valuations independent of the
absolute meter; arises from `tilt_cap` and the **second stopped scale** of the true Scribes.
No support omissions beyond scope of precursor proofs for Fare and quota that retain them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C: Family G} {𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) (hG:G.Simple){H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable {J:Scaling S}{V:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}
variable (hV:Gondola f H J 𝓛 V Y)(hk:PostT C.path.levels)
set_option quotPrecheck false
local notation "A!" => C.path.levels
local notation "T!" => C.labels
local notation "B!" => Climb.Bel C.book
local notation "X!" => (𝓛:Filter (ℕ×ℕ))
local notation "β!" => (A!).clock.hatBeta
local notation "P!" => (A!).clock.monitor
local notation "D!" => β!

lemma pastTilt (P:Levels G)(hG:G.Simple) : ∀ᶠ i in atTop,tilt_cap P i ≤ P.clock.hatBeta i:=by
   let X(i:ℕ):= Lyra P i
   have hf : ∀ᶠ x:ℝ in atTop, Real.log x ^ 3 ≤ x:=by
      filter_upwards [Real.isLittleO_pow_log_id_atTop (n:=3)|>.bound one_pos,eventually_ge_atTop (1:ℝ)] with x hx ht
      simpa only [one_mul,id_eq, Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg ht) 3),Real.norm_of_nonneg (zero_le_one.trans ht)] using! hx
   filter_upwards [(lrate P hG).eventually hf] with i hi
   change (Real.exp ((Real.log (X i))^2))^(Real.log (X i)) ≤ _
   rw [← Real.exp_mul]; refine le_trans (Real.exp_monotone (b:=X i) ?_) ((Real.exp_log (bell ..)).le); exact (pow_succ (Real.log (X i)) 2).symm ▸ hi -- direction

lemma monitor_upper (P:Levels G)(hG:G.Simple) : ∀ᶠ k in atTop,P.clock.monitor k ≤ P.clock.hatBeta k:= ((hat_rate P hG).eventually (Vac.Numbers.cost 1 1 one_pos)).mono fun i hi=> by simpa only [Real.rpow_one] using! hi
lemma exp_in (d:ℕ)(j:ℕ)(b:ℝ) : 0≤ preExpense C d j b:=by unfold preExpense preExpense.pre_billing; positivity
include hG hV
lemma exp_boat (d:ℕ): ∃ (K:ℝ)(t:ℕ),1 ≤ K ∧ ∀ᶠ i in atTop, let j:=(V i).k; preExpense C d j (V i).b ≤ K * (β! j) ^ t := by
   let F':Frame G d:=C.labels.level d;let s := ∑ i : F'.Index, ((F'.grades i).1+(F'.grades i).2)
   let c:ℝ:=2^s; let b:ℝ:= 2*(Fintype.card F'.Index)*c
   refine ⟨max 1 b, s, le_max_left .., ?_⟩
   filter_upwards [hV.growth.eventually (pastTilt A! hG),hV.growth.eventually (monitor_upper A! hG)] with i hQ hA j
   let x:= β! j; let B:= mag (A!) (V i).b j; have hx:1<x:= (A!).fits.delayed _
   have h : B ≤ x:= le_trans (tiltP (C:=C) _ (hV.season i|>.1.high.2)) hQ
   have hv:0≤B:= (mag_pos ..).le
   let z:= 2*(P! j); change 2*(∑ i:F'.Index, ‖z^(F'.grades i).2*B^(F'.grades i).1‖)≤_*x^s
   have hp:0 ≤ z:=mul_nonneg zero_le_two (Real.exp_pos _).le
   have h₁(i:F'.Index) := Finset.single_le_sum (f:=fun i:F'.Index=>(F'.grades i).1+(F'.grades i).2) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
   let A(i:F'.Index):=(F'.grades i).1; let D(i:F'.Index):=(F'.grades i).2; have hh(i:F'.Index):A i+D i≤ s:= h₁ i
   have hu:z≤2*x:= mul_le_mul_of_nonneg_left hA zero_le_two
   have hc(i:F'.Index): ‖z^D i*B^A i‖ ≤ c*x^s:=by
      rw [Real.norm_of_nonneg (by positivity)]; refine (mul_le_mul (pow_le_pow_left₀ hp hu _) (pow_le_pow_left₀ hv h _) (by positivity) (by positivity)).trans ?_
      rw [mul_pow, mul_assoc, ← pow_add]; refine mul_le_mul (pow_le_pow_right₀ one_le_two (by linarith only [hh i])) (pow_le_pow_right₀ hx.le (by linarith only [hh i])) (pow_nonneg (zero_le_one.trans hx.le) _) (show 0≤c by unfold c; positivity)
   apply le_trans (b:=2*(∑ _i : F'.Index,c*x^s)) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hc i)) zero_le_two); apply le_trans (b:=b*x^s) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)); simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold b; exact Eq.le (by ring)

lemma anchorage : ∃ C':ℝ,1≤ C'∧∀ᶠ i in atTop, β! (V i).k ≤ C'*dock (J.r i):=by
   let t:= G.slopeConstant⁻¹; have hT: 0<t:=inv_pos.mpr (Gauge.slopeConstant_pos hG); let b:= (t/2)⁻¹; refine ⟨max b 1, le_max_right .., ?_⟩
   filter_upwards [(log_hat hV hG).eventually (lt_mem_nhds (half_lt_self hT)),J.drips.eventually (ge_mem_nhds zero_lt_one)] with i hv hi
   have hx:t/2≤ LogV (J.r i)/(β! (V i).k):= hv.le; have hb:0 < b:= by unfold b; positivity
   have h₁: LogV (J.r i) ≤ dock (J.r i):=by unfold dock; linarith
   apply (((le_inv_mul_iff₀ (by positivity : 0<t/2)).2 ((le_div_iff₀ (bell ..)).1 hx)).trans ?_); exact mul_le_mul_of_nonneg_left h₁ hb.le|>.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans (dock_valid _ ⟨J.positive i,hi⟩))) -- precedence

structure Turnkey (F:Final C f S)(𝓛: Ultrafilter (ℕ×ℕ))(r:ℝ)(j m d:ℕ)(B:ℝ) : Prop where
   owns : C.ref d≤ j
   coin (v:S.Field d): ∃ (Z:C.label d)(Y:ℕ×ℕ→C.label d), S.project d Z=v ∧ Tendsto Y (𝓛:Filter (ℕ×ℕ)) (𝓝 Z) ∧ ∀ᶠ u:ℕ×ℕ in (𝓛:Filter (ℕ×ℕ)), Next.UVStress.quota C d j u.1 u.2 (Y u) ≤ C.S.a j^d*B*cost F d r v ∧ Cards.PaidAt C.S u.1 u.2 m (C.beta u.1 u.2) (B * cost F d r v) (C.O u.1 u.2 (Y u) 0)

omit hG hV
lemma Turnkey.le {r B A:ℝ}{j m d:ℕ}(h:Turnkey F 𝓛 r j m d A)(he:A≤B): Turnkey F 𝓛 r j m d B := by
   refine ⟨h.owns,fun v=>?_⟩; obtain ⟨Z,Y,hV,hY,hK⟩:=h.coin v
   refine ⟨Z,Y,hV,hY,hK.mono fun i hi=>?_⟩
   exact ⟨hi.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (pow_nonneg (C.S.a_pos _).le _)) (Ascent.cost_pos ..)), hi.2.live, hi.2.ticket, hi.2.mark.trans (mul_le_mul_of_nonneg_right he (Ascent.cost_pos ..))⟩

include hG hV
-- linear-ticket selection (may depend on grid but use before psi)
variable (hX:𝓛.toFilter ≤ f.fuse)
include hX F
lemma wall_budget (d:ℕ) : ∃ B:ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, let m:= purchaseWidth (V i); ∀ v:(Bel C.book).Field d,∀ᶠ u:ℕ×ℕ in X!, Cards.PaidAt C.S u.1 u.2 m (C.beta u.1 u.2) (B * ‖v‖) (C.O u.1 u.2 (heightV V i d u v) 0) :=by
   let K:Module.Basis (PegC C d) ℂ ((Bel C.book).Field d) := PoleC C d -- fix
   choose A ha hv using fun t:PegC C d=> pair_origin hX hV F.room.cutoff 1 (by norm_num) one_lt_two hG t
   let y(t:PegC C d):= (K.coord t).toContinuousLinearMap; let B:= ∑ t:PegC C d, ‖y t‖ * A t
   refine ⟨max 1 B, le_max_left .., ?_⟩; filter_upwards [eventually_all.mpr hv] with i hi m v
   let a(t:PegC C d):= K.repr v t
   filter_upwards [eventually_all.mpr hi,(link_mesh hX).eventually_ge_atTop m] with u hu hM
   change m≤u.1 at hM
   let p:= Cells.center C.S u.2 hM 0; let β:=C.beta u.1 u.2; let f:= ((C.linearO u.1 u.2 d 0).mk' _).comp (heightV V i d u).toLinearMap
   have hx(t:PegC C d): Cells.Interior (p.chamber 0) (f (K t)) ∧ p.rootTest β (f (K t))≤ A t:= (hu t).choose_spec.2 0
   change OPE.Cards.PaidAt _ _ _ _ _ _ (f v);
   obtain ⟨hO,hP⟩:= Next.Extract.rooted p β (Cells.seamless F.room.cutoff ..) Finset.univ (fun t=> f (K t)) a (fun i _=> (hx i).1)
   have hf : f v=∑ t, a t • f (K t):=by
      conv_lhs=> rw [← K.sum_repr v,map_sum]
      simp_rw [map_smul]; rfl -- semicolon conv bug
   rw [hf]; refine ⟨hM,hO,hP.trans (le_trans (b:=B*‖v‖) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)))⟩
   unfold B; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun i _=>?_); rw [mul_right_comm ‖y i‖]; refine mul_le_mul ((y i).le_opNorm v) (hx i).2 (Cells.Tiling.root_nonneg ..) (by positivity)
lemma buoyant (h:Scribe f J V Z F.sector 𝓛 F.room.kernel H) (d:ℕ) :∃ (A:ℝ)(m:ℕ),1 ≤ A ∧ ∀ᶠ i in atTop, Turnkey F 𝓛 (J.r i) (V i).k (purchaseWidth (V i)) d (A*dock (J.r i)^m) :=by
   obtain ⟨C',hc,hQ⟩:= wall_budget F hG hV hX d
   obtain ⟨K,t,hK,hE⟩:= exp_boat hG hV d
   obtain ⟨D,hD,hG'⟩:= anchorage hG hV
   obtain ⟨B,hB,hU⟩:= window_prices F hG h.monorail d 1 1 one_pos
   let T:= ladder C d; let A:ℝ:= K*D^t * ‖T‖ * B; have hK':0 ≤ K:=zero_le_one.trans hK
   refine ⟨max A (C'*B),t,(one_le_mul_of_one_le_of_one_le hc hB).trans (le_max_right ..),?_⟩
   filter_upwards [hV.terminal d,eventually_ge_atTop d,hU,hG',hE,hQ,J.drips.eventually (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with i hi hd hh he hu hQ hp
   let w:Fin (i+1):=⟨d,Nat.lt_succ_of_le hd⟩; let j:=(V i).k
   have hV':=(hV.season i).1
   have hz : 1 ≤ dock (J.r i):= dock_valid _ ⟨J.positive _, hp⟩
   refine ⟨hV'.early w,fun x=> ?_⟩
   obtain ⟨v,rfl⟩:= (J.U i d).surjective x
   refine ⟨Y d i v,fun z=> heightV V i d z v,(hi.2 v).symm,Dash.arcing hi.1 tendsto_const_nhds,?_⟩
   filter_upwards [hQ v,(link_mesh hX).eventually_gt_atTop j] with u hu' hN
   let y:=cost F d (J.r i) (J.U i d v)
   have ht:= (hh v).1; have hx:0 ≤ y:=Ascent.cost_pos ..; have hy:1 ≤ C'*B:=one_le_mul_of_one_le_of_one_le hc hB; let b:ℝ:=max A (C'*B)
   constructor
   · let Z:=(V i).R u.1 u.2 w; let M:=preExpense C d j (V i).b
     have h:= hV'.early w; have hT: Next.Rank.Price.Tested C w j u.1 u.2 Z:= ((hV'.rate u.1 u.2 hN).1 w).1
     let a:= C.S.a j; have ha:0<a:= C.S.a_pos _; have hv:M ≤ K*D^t * dock (J.r i)^t:= (hu.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (bell ..|>.le) he t) hK').trans_eq (by rw [mul_pow, mul_assoc])))
     have he': ‖T v‖ ≤ ‖T‖*(B*y):=(T.le_opNorm v).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
     simp only [heightV, dif_pos hd]; refine (quotation C (b:=(V i).b) (N:=u.1) (p:=u.2) d j F.room.cutoff (hV'.early w) hN.le Z hT (T v)).trans ?_
     unfold signal; change _ ≤ a^d* (b*_)*y; have hZ:a^d * M * ‖T v‖ ≤ a^d*(K*D^t*dock (J.r i)^t)*(‖T‖*(B*y)):=mul_le_mul (mul_le_mul_of_nonneg_left hv (by positivity)) he' (norm_nonneg _) (by positivity)
     refine hZ.trans (le_trans (b:=a^d*(A*dock (J.r i)^t)*y) ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity : 0 ≤ dock (J.r i)^t)) (by positivity : 0 ≤ a^d)) hx)); apply Eq.le
     unfold A; ring
   refine ⟨hu'.live,hu'.ticket,hu'.mark.trans ?_⟩; refine le_trans (b:=(C'*B)*y) ?_ (mul_le_mul_of_nonneg_right ((le_max_right A _).trans (le_mul_of_one_le_right (zero_le_one.trans (hy.trans (le_max_right ..))) (one_le_pow₀ hz))) hx); rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht (zero_le_one.trans hc)

structure Pool (F:Final C f S)(𝓛:Ultrafilter (ℕ×ℕ))(r:ℝ)(j m D:ℕ)(A:ℝ):Prop where
   fore : m≤j
   breadth : r<(A * C.S.a j)
   front : C.S.a m<r*A
   budget : ∀ d≤D, Turnkey F 𝓛 r j m d A

include hk
lemma pond (h:Scribe f J V Z F.sector 𝓛 F.room.kernel H) (d:ℕ) :∃ (A:ℝ)(t:ℕ), 1≤A ∧ ∀ᶠ i in atTop,Pool F 𝓛 (J.r i) (V i).k (purchaseWidth (V i)) d (A*dock (J.r i)^t) :=by
   obtain ⟨C',hC,hQ⟩:= anchorage hG hV; choose A m hA hf using fun i:Fin (d+1)=> buoyant F hG hV hX h i
   obtain ⟨M,hM,ht⟩:= ((eventually_gt_atTop C').and (eventually_all.mpr fun i=> eventually_ge_atTop (A i))).exists
   obtain ⟨t,h₁,h₂⟩:= ((eventually_ge_atTop 1).and (eventually_all.mpr fun i=> eventually_ge_atTop (m i))).exists
   have he:=hC.trans_lt hM
   refine ⟨M,t,he.le,?_⟩
   filter_upwards [hQ,eventually_all.mpr hf,overhang hV hG hk,hV.growth.eventually (pastTilt A! hG),J.drips.eventually (ge_mem_nhds zero_lt_one)] with i hi hv hz hb hh
   let r:= J.r i; let a:= (C.S.a (V i|>.k)); let y:= dock r; let w:=purchaseWidth (V i); have hr:0<r:=J.positive _; have hp:1 ≤ y:= dock_valid _ ⟨hr,hh⟩
   have hy:y≤y^t:=by simpa only [pow_one] using pow_le_pow_right₀ hp h₁
   have hm : y ≤ M*y^t:= hy.trans (le_mul_of_one_le_left (by positivity) he.le)
   refine ⟨(widerSky ..).trans (beforeSky ..),?_,?_,fun j hg=>?_⟩
   · nth_rw 1 [show J.r i=a*mag A! (V i).b (V i).k from (hV.season i).2.symm, mul_comm a]; have he : C'*y < M*y:=mul_lt_mul_of_pos_right hM (by positivity)
     apply mul_lt_mul_of_pos_right _ (C.S.a_pos _); exact (le_trans (tiltP (C:=C) _ (hV.season i|>.1.high.2)) (hb.trans hi)).trans_lt (he.trans_le (mul_le_mul_of_nonneg_left hy (by positivity))) -- he shadow
   · apply lt_of_le_of_lt (C.S.strictAnti.antitone (Nat.sub_le w 1)) (hz.2.2.trans_le ?_); rw [mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ hr.le; refine le_trans ?_ hm; change LogV r/32 ≤ y; have h: LogV r ≤ y:=by unfold y dock; linarith
     linarith only [h,hp]
   let u:Fin (d+1):= ⟨j,Nat.lt_succ_of_le hg⟩; have hh :0 ≤ y^m u:=by positivity
   exact (hv u).le F (mul_le_mul (ht u) (pow_le_pow_right₀ hp (h₂ u)) hh (zero_le_one.trans he.le))

omit hV hX hk in
lemma every_pool (H:Bliss F 𝓛 Z H)(d:ℕ) :∃ (t:ℕ),∀ᶠ r in trail,∃ j m,Pool F 𝓛 r j m d (dock r^t):=by
   -- contradiction using exponent growing, not re-meet schedule across ALL ξ fields
   by_contra! hx
   have ht(i:ℕ):∃ s:ℝ,0<s ∧ s<Next.UVStress.costHint i ∧ ∀ j m, ¬ Pool F 𝓛 s j m d (dock s^i):= by
      obtain ⟨s,h,h1,h2⟩:= ((hx i).and_eventually ((show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).and ((gt_mem_nhds (Next.UVStress.cost_pos i)).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨s,h1,h2,h⟩
   choose s hs h' he using ht
   obtain ⟨m,hm,J,hJ,V,hV⟩:= H.picks s (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Next.UVStress.cost_clears (fun i=> (hs i).le) (fun i=>(h' i).le)) hs
   obtain ⟨Y,hY⟩:=hV.meters
   obtain ⟨B,t,hB,hK⟩:= pond F hG hY H.budgets H.lies hV d
   have hv:Tendsto (fun i=> dock (J.r i)) atTop atTop:= tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=J))
   obtain ⟨i,⟨hi,hI⟩,hM⟩:= ((hK.and (hv.eventually_ge_atTop B)).and (hm.tendsto_atTop.eventually_ge_atTop (t+1))).exists -- unpack
   apply he (m i) (V i).k (purchaseWidth (V i))
   change B ≤ dock (J.r i) at hI
   have hp:0<J.r i:=J.positive _
   rw [hJ] at hi hp hI; change s (m i) > 0 at hp
   let r:= s (m i); let y:=dock r; change B≤y at hI; have hh:B*y^t≤ y^(m i):=(mul_le_mul_of_nonneg_right hI (show 0 ≤ y^t from pow_nonneg (zero_le_one.trans (hB.trans hI)) _)).trans ((pow_succ' y t).symm.le.trans (pow_le_pow_right₀ (hB.trans hI) hM))
   exact ⟨hi.fore,hi.breadth.trans_le (mul_le_mul_of_nonneg_right hh (C.S.a_pos _|>.le)), hi.front.trans_le (mul_le_mul_of_nonneg_left hh hp.le),fun j hj=> (hi.budget j hj).le F hh⟩
end YM.GapsContact.Seams
