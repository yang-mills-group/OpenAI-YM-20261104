import YM.GapsContact.Earn.Buoys
import YM.Integration.WilsonThermometerUnitFilingFourWall
/-! One shared reporter and one linear station map for all public inputs at a
given grade. The raw quota holds for every period once the top is above the
station. The reflected card uses the original ordered cutoff filter. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPool
open GapsContact GapsContact.Seams GapsContact.Stamps
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


structure BookedArm (F : Final C f S) (l : Ultrafilter (ℕ×ℕ)) (r : ℝ) (j m d : ℕ) (B : ℝ) : Prop where
  owns : C.ref d≤j
  station : ∃ (V : ∀ k : ℕ, Vane C k) (k₀ : ℕ) (ok : d ≤ k₀) (T : Spin.change S d)
    (Z : (Cells.standard C).Field d →L[ℂ] C.label d),
    (V k₀).k=j ∧ purchaseWidth (V k₀)=m ∧
    (∀ v, S.project d (Z v)=T v) ∧ Tendsto (heightV V k₀ d) (l:Filter (ℕ×ℕ)) (𝓝 Z) ∧
    ∀ v : (Cells.standard C).Field d,
      let Y := fun u : ℕ×ℕ => (V k₀).wheel.atCut u ⟨d,Nat.lt_succ_of_le ok⟩ v
      (∀ N p, j<N → Next.UVStress.quota C d j N p (Y (N,p)) ≤ C.S.a j^d*B*cost F d r (T v)) ∧
      ∀ᶠ u : ℕ×ℕ in f.fuse, Cards.PaidAt C.S u.1 u.2 m (C.beta u.1 u.2)
        (B*cost F d r (T v)) (C.O u.1 u.2 (Y u) 0)

lemma BookedArm.le {r A B : ℝ} {j m d : ℕ} (h : BookedArm F 𝓛 r j m d A) (up : A≤B) :
    BookedArm F 𝓛 r j m d B := by
  obtain ⟨V,i,ad,T,Z,here,reach,base,tends,old⟩ := h.station
  refine ⟨h.owns,V,i,ad,T,Z,here,reach,base,tends,fun v=>?_⟩
  have e := Ascent.cost_pos F d r (T v)
  have bought := old v
  exact ⟨fun N p later=>(bought.1 N p later).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left up (pow_nonneg (C.S.a_pos _).le _)) e),
    bought.2.mono fun _ card=>⟨card.live,card.ticket,card.mark.trans (mul_le_mul_of_nonneg_right up e)⟩⟩

include hG hV
-- linear-ticket selection (may depend on grid but use before psi)
include F
private lemma reflected (d:ℕ) : ∃ B:ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, let m:= purchaseWidth (V i); ∀ v:(Bel C.book).Field d,∀ᶠ u:ℕ×ℕ in f.fuse, Cards.PaidAt C.S u.1 u.2 m (C.beta u.1 u.2) (B * ‖v‖) (C.O u.1 u.2 (heightV V i d u v) 0) :=by
   let K:Module.Basis (PegC C d) ℂ ((Bel C.book).Field d) := PoleC C d -- fix
   choose A ha hv using fun t:PegC C d=> WilsonThermometerUnitFilingFourWall.original hV F.room.cutoff 1 (by norm_num) one_lt_two hG t
   let y(t:PegC C d):= (K.coord t).toContinuousLinearMap; let B:= ∑ t:PegC C d, ‖y t‖ * A t
   refine ⟨max 1 B, le_max_left .., ?_⟩; filter_upwards [eventually_all.mpr hv] with i hi m v
   let a(t:PegC C d):= K.repr v t
   have mesh : ∀ᶠ u:ℕ×ℕ in f.fuse, m≤u.1 := by
     rw [Extraction.Order.fused]; unfold Extraction.Order.late
     exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop m
   filter_upwards [eventually_all.mpr hi,mesh] with u hu hM
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
private lemma authentic (h:Scribe f J V Z F.sector 𝓛 F.room.kernel H) (d:ℕ) :∃ (A:ℝ)(m:ℕ),1 ≤ A ∧ ∀ᶠ i in atTop, BookedArm F 𝓛 (J.r i) (V i).k (purchaseWidth (V i)) d (A*dock (J.r i)^m) :=by
   obtain ⟨C',hc,hQ⟩:= reflected F hG hV d
   obtain ⟨K,t,hK,hE⟩:= exp_boat hG hV d
   obtain ⟨D,hD,hG'⟩:= anchorage hG hV
   obtain ⟨B,hB,hU⟩:= window_prices F hG h.monorail d 1 1 one_pos
   let T:= ladder C d; let A:ℝ:= K*D^t * ‖T‖ * B; have hK':0 ≤ K:=zero_le_one.trans hK
   refine ⟨max A (C'*B),t,(one_le_mul_of_one_le_of_one_le hc hB).trans (le_max_right ..),?_⟩
   filter_upwards [hV.terminal d,eventually_ge_atTop d,hU,hG',hE,hQ,J.drips.eventually (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with i hi hd hh he hu hQ hp
   let w:Fin (i+1):=⟨d,Nat.lt_succ_of_le hd⟩; let j:=(V i).k
   have hV':=(hV.season i).1
   have hz : 1 ≤ dock (J.r i):= dock_valid _ ⟨J.positive _, hp⟩
   refine ⟨hV'.early w,V,i,hd,J.U i d,Y d i,rfl,rfl,(fun v=>(hi.2 v).symm),hi.1,fun v=>?_⟩
   let y:=cost F d (J.r i) (J.U i d v)
   have ht:= (hh v).1; have hx:0 ≤ y:=Ascent.cost_pos ..; have hy:1 ≤ C'*B:=one_le_mul_of_one_le_of_one_le hc hB; let b:ℝ:=max A (C'*B)
   constructor
   · intro N p hN
     let u : ℕ×ℕ := (N,p)
     let Z:=(V i).R u.1 u.2 w; let M:=preExpense C d j (V i).b
     have h:= hV'.early w; have hT: Next.Rank.Price.Tested C w j u.1 u.2 Z:= ((hV'.rate u.1 u.2 hN).1 w).1
     let a:= C.S.a j; have ha:0<a:= C.S.a_pos _; have hv:M ≤ K*D^t * dock (J.r i)^t:= (hu.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (bell ..|>.le) he t) hK').trans_eq (by rw [mul_pow, mul_assoc])))
     have he': ‖T v‖ ≤ ‖T‖*(B*y):=(T.le_opNorm v).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
     refine (quotation C (b:=(V i).b) (N:=u.1) (p:=u.2) d j F.room.cutoff (hV'.early w) hN.le Z hT (T v)).trans ?_
     unfold signal; change _ ≤ a^d* (b*_)*y; have hZ:a^d * M * ‖T v‖ ≤ a^d*(K*D^t*dock (J.r i)^t)*(‖T‖*(B*y)):=mul_le_mul (mul_le_mul_of_nonneg_left hv (by positivity)) he' (norm_nonneg _) (by positivity)
     refine hZ.trans (le_trans (b:=a^d*(A*dock (J.r i)^t)*y) ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity : 0 ≤ dock (J.r i)^t)) (by positivity : 0 ≤ a^d)) hx)); apply Eq.le
     unfold A; ring
   filter_upwards [hQ v] with u wall
   simp only [heightV,dif_pos hd] at wall
   refine ⟨wall.live,wall.ticket,wall.mark.trans ?_⟩; refine le_trans (b:=(C'*B)*y) ?_ (mul_le_mul_of_nonneg_right ((le_max_right A _).trans (le_mul_of_one_le_right (zero_le_one.trans (hy.trans (le_max_right ..))) (one_le_pow₀ hz))) hx); rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht (zero_le_one.trans hc)

structure Receipt (F:Final C f S)(𝓛:Ultrafilter (ℕ×ℕ))(r:ℝ)(j m D:ℕ)(A:ℝ):Prop where
   fore : m≤j
   breadth : r<(A * C.S.a j)
   front : C.S.a m<r*A
   budget : ∀ d≤D, BookedArm F 𝓛 r j m d A

include hk
private lemma cards (h:Scribe f J V Z F.sector 𝓛 F.room.kernel H) (d:ℕ) :∃ (A:ℝ)(t:ℕ), 1≤A ∧ ∀ᶠ i in atTop,Receipt F 𝓛 (J.r i) (V i).k (purchaseWidth (V i)) d (A*dock (J.r i)^t) :=by
   obtain ⟨C',hC,hQ⟩:= anchorage hG hV; choose A m hA hf using fun i:Fin (d+1)=> authentic F hG hV h i
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

omit hV hk in
theorem original (H:Bliss F 𝓛 Z H)(d:ℕ) :∃ (t:ℕ),∀ᶠ r in trail,∃ j m,Receipt F 𝓛 r j m d (dock r^t):=by
   -- contradiction using exponent growing, not re-meet schedule across ALL ξ fields
   by_contra! hx
   have ht(i:ℕ):∃ s:ℝ,0<s ∧ s<Next.UVStress.costHint i ∧ ∀ j m, ¬ Receipt F 𝓛 s j m d (dock s^i):= by
      obtain ⟨s,h,h1,h2⟩:= ((hx i).and_eventually ((show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).and ((gt_mem_nhds (Next.UVStress.cost_pos i)).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨s,h1,h2,h⟩
   choose s hs h' he using ht
   obtain ⟨m,hm,J,hJ,V,hV⟩:= H.picks s (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Next.UVStress.cost_clears (fun i=> (hs i).le) (fun i=>(h' i).le)) hs
   obtain ⟨Y,hY⟩:=hV.meters
   obtain ⟨B,t,hB,hK⟩:= cards F hG hY H.budgets hV d
   have hv:Tendsto (fun i=> dock (J.r i)) atTop atTop:= tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=J))
   obtain ⟨i,⟨hi,hI⟩,hM⟩:= ((hK.and (hv.eventually_ge_atTop B)).and (hm.tendsto_atTop.eventually_ge_atTop (t+1))).exists -- unpack
   apply he (m i) (V i).k (purchaseWidth (V i))
   change B ≤ dock (J.r i) at hI
   have hp:0<J.r i:=J.positive _
   rw [hJ] at hi hp hI; change s (m i) > 0 at hp
   let r:= s (m i); let y:=dock r; change B≤y at hI; have hh:B*y^t≤ y^(m i):=(mul_le_mul_of_nonneg_right hI (show 0 ≤ y^t from pow_nonneg (zero_le_one.trans (hB.trans hI)) _)).trans ((pow_succ' y t).symm.le.trans (pow_le_pow_right₀ (hB.trans hI) hM))
   exact ⟨hi.fore,hi.breadth.trans_le (mul_le_mul_of_nonneg_right hh (C.S.a_pos _|>.le)), hi.front.trans_le (mul_le_mul_of_nonneg_left hh hp.le),fun j hj=> (hi.budget j hj).le F hh⟩
end YM.Integration.WilsonThermometerUnitFilingFourPool
