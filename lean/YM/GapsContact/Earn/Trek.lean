import YM.GapsContact.Earn.Windrose

/-!
# Wind into the moving forest

The parking receipt is priced towards measuring units on actual theory. Integrating exterior
buds may pay their OWN clearance, no replacement until `look` is seated against its future
listeners (possibly at different radii closer/farther than the main purchasing length).
Use forest contact versions in the same phase and theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Set Function Filter MeasureTheory Analysis Spec Table Extraction Lattice RG Wilson
open Frontier6 Frontier6.Tale Ascent Power Trace Trace.Terrace Trace.Pilot
open OPE OPE.Log
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V:Type} [Fintype I][Fintype J]{G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F: Final C f S) {l:Filter V}
variable {T g R t y:V→ℝ}{a b c ε:ℝ} {q j m:V→ℕ}
universe u
variable {hG:G.Simple}{A:EveryPhase.Almanac F}
variable {d n:ℕ} (H:Roll.{u} F hG A)
local notation "α!"=> C.S.a
local notation "λ'"=> C.S.gridPoint
local notation "n'"=> Fintype.card I

lemma exact_shift {x z:V→ℝ}{w:V→S.Field d}{l':ℝ} (hT:Tendsto T l atTop)(h:∀ᶠ i in l,x i∈Ioc 0 (1:ℝ) ∧ z i∈ Ioc 0 (x i))(hr:RateIs l T (fun i=>x i/z i) a) (hw:RateLE l T (fun i=> cost F d (x i) (w i)) l') (Z:Market F d 1 1 b) : RateLE l T (fun i=> cost F d (z i) (w i)) (((d:ℝ)+1)*a+l') := by
    refine (((RateLE.const b hT).mul ((hr.rpow ((d:ℝ)+1)).pays hT)).mul hw).mono (le_of_eq (by rw[zero_add]))|>.of_norm_le ?_; filter_upwards [h] with i hi; rw [Real.norm_of_nonneg (Ascent.cost_pos ..)]; exact Z.left hi.1 hi.2 _

-- pure geometry estimator: halls footprint postage from crop. build three levels.
def plunge (s:V→ℝ)(a:ℝ)(T:V→ℝ)(i:V):= s i*Real.exp (-a*T i)
variable {𝓛:Ultrafilter (ℕ×ℕ)} {Q:(Climb.Bel C.book).Hierarchy} {Z: Arch C}
variable (H':Bliss F 𝓛 Z Q) (hT:Tendsto T l atTop)
include hT
lemma sink_rate (ht:Ridge l T g)(ha:0<a): RateIs l T (fun i=> plunge g a T i/g i) (-a) := relation_inv ((ht.motion hT ha).2.2.2)
lemma tidal (hp:RateIs l T (fun i=>g i/t i) a)(hb:0<a)(ht:∀ᶠ i in l, 0<t i)(c:ℝ) : ∀ᶠ i in l, c*t i < g i := by
    filter_upwards [hp.overtakes (RateLE.const c hT) hT hb,ht] with i hi ht using (lt_div_iff₀ ht).mp hi
variable (hA:Ridge l T t) (hy:Ridge l T y) (hq:Layer C l T q) (hp:RateIs l T (fun i=>t i/C.S.a (q i)) ε) (he:0<ε) (hR:∀ᶠ i in l, y i≤ t i)
local notation "s!" => plunge y (3*ε) T
-- support arrangement over ext radius y and t phase clearance. n occupants. No spec on t's behavior vs T.
include H' H hA hy hq hp he hR
omit H hq in
lemma archipel (hG:G.Simple)(d' n:ℕ) : ∃ (B L J N:V→ℕ) (D':V→ℝ), RateIs l T D' 0 ∧ ∀ᶠ i in l, B i ≤ q i ∧ 2*α! (B i)< t i ∧ 2*α! (L i) < y i ∧ Cards.Hall C.S (B i) (L i) (q i) (q i) (N i) 1 n ∧ Pool F 𝓛 (plunge y (3*ε) T i) (J i) (N i) d' (D' i):= by
    obtain ⟨B,-,-,-,-,h₁,-,-,-⟩:= locate hT F hG H' 0 ((hA.motion hT (half_pos he)).1) ((hA.motion hT (half_pos he)).2.1)
    have hy' : Ridge l T (plunge y (2*ε) T) := (hy.motion hT (by positivity : 0<2*ε)).1
    obtain ⟨L,-,-,-,-,h₂,-,-,-⟩:= locate hT F hG H' 0 hy' ((hy.motion hT (by positivity : 0<2*ε)).2.1)
    have hz : Ridge l T (plunge y (3*ε) T) := (hy.motion hT (by positivity : 0<3*ε)).1
    obtain ⟨J,N,D',hJ,hN,h₃,h₄,hD,hP⟩:= locate hT F hG H' d' hz ((hy.motion hT (by positivity : 0<3*ε)).2.1)
    have hB : RateIs l T (fun i=>α! (B i)/t i) (-(ε/2)) := (relation_mul ((hA.motion hT (half_pos he)).1.pos.mono (fun i hi=> hi.ne')) h₁ (sink_rate hT hA (half_pos he))).swap (zero_add _)
    have hL : RateIs l T (fun i=>α! (L i)/y i) (-(2*ε)) := (relation_mul (hy'.pos.mono fun i hi=> hi.ne') h₂ (sink_rate hT hy (by positivity))).swap (zero_add _)
    have hN: RateIs l T (fun i=>α! (N i)/y i) (-(3*ε)) := (relation_mul (hz.pos.mono fun i hi=> hi.ne') h₄ (sink_rate hT hy (by positivity))).swap (zero_add _)
    have hV:= relation_mul (hA.pos.mono fun i hi=>hi.ne') hB hp; have hY:= relation_mul (hy.pos.mono fun i hi=>hi.ne') hL (relation_inv hN)
    have hf(X:V→ℕ):∀ᶠ i in l, 0 < C.S.a (X i):= Eventually.of_forall fun i=>C.S.a_pos _
    refine ⟨B,L,J,N,D',hD,?_⟩
    filter_upwards [tower_earlier hT hV (by linarith), tidal hT hV (by linarith) (hf q) 10, tower_earlier hT hY (by linarith), tidal hT hY (by linarith) (hf N) (6*n), tidal hT (relation_inv hB) (by linarith) (hf B) 2, tidal hT (relation_inv hL) (by linarith) (hf L) 2, (relation_inv hp).overtakes (hL.pays hT) hT (by linarith),hA.pos,hy.pos,hP,hR] with i hi hx hl hm hb ht hk hu hv hy hz
    have he':q i ≤ L i:= by
       apply C.S.strictAnti.le_iff_ge.mp
       apply (div_le_div_iff_of_pos_right hu).1; exact (div_le_div_of_nonneg_left (C.S.a_pos _).le hv hz).trans hk.le
    refine ⟨hi.le,hb,ht,⟨hi.le,he',le_rfl,hl.le,?_,?_⟩,hy⟩ <;> push_cast <;> linarith only [hx,hm]

omit hq hA hy hp he hR H' H hT
variable (e:J→ℕ)
variable {w:J→ℝ}
lemma price_tall (e:J→ℕ): ∃ w:ℕ,∀j,e j ≤ w := (eventually_all.mpr fun j=>eventually_ge_atTop (e j)).exists
-- include hR Balcony needs
variable {z:V→I→ Cover}{u: V→ I→ S.Tag}{x:V→ S.Field d}{o C': V→ℝ}
variable (k:V→ StateIndex F)(e:J→ℕ)
include hT H' H hA hy hp he hR
lemma islands (hF: Org.Grill C f)(hs:∀ᶠ i in l, Screen (C.S.gridPoint (j i) ∘ z i)) (hb:∀ᶠ i in l,q i ≤ j i) (h:∀ᶠ i in l, Stall (C:=C) 𝓛 S (q i) (m i) (j i) (o i) (C' i) d (z i) (u i) (x i)) (ho:RateLE l T o a)
     (Y: V→ J→ E4)
     (B:∀i:J,V→ S.Field (e i))(w:J→ℝ)
     (hv:∀ᶠ i in l, Balcony (g i) (y i) (t i) (Y i) 0 ∧ Injective (beside (λ' (j i) ∘ z i) (Y i))) (hx:∀ i:J,RateLE l T (fun k=> cost F (e i) (y k) (B i k)) (w i)) :
   RateLE l T (fun i=> peal F (k i) ((assembly S (λ' (j i) ∘ z i) (u i) - letter S 0 ⟨d,x i⟩) * spendsWord (S:=S) (Y i) e (fun j=> B j i))) (a+∑ i:J, ( ((e i:ℝ)+1)*(3*ε)+w i)):=by -- sum parse
   obtain ⟨w',hw⟩:= price_tall e; obtain ⟨B',L,J',N,D',hD,hQ⟩:= archipel F H' hT hA hy hp he hR hG w' (Fintype.card J) -- order
   let s:= plunge y (3*ε) T; have he':0<3*ε:=(by positivity); have hy':= hy.motion hT he'
   have hg:∀ i:J, RateLE l T (fun k=>D' k * cost F (e i) (s k) (B i k)) ( ((e i:ℝ)+1)*(3*ε)+w i):=by
       intro i; obtain ⟨c,hc⟩:= token_grants F H (e i) 1 one_pos; refine ((hD.pays hT).mul (exact_shift F hT (z:=s) ?_ hy'.2.2.2 (hx i) hc)).mono (le_of_eq (zero_add _)); exact hy.soon.and (((hy'.1).pos.and hy'.2.2.1).mono fun i hi=>⟨hi.1,hi.2⟩)
   refine (ho.mul (RateLE.prod (f:=fun i:J=>fun k:V=>D' k * cost F (e i) (s k) (B i k)) hT fun i _=> hg i)).of_norm_le ?_
   filter_upwards [h,hb,hv,hQ,hs] with i hi hb ⟨hV,hI⟩ ⟨h',hB,hL,hQ,hY⟩ hs
   exact stall_emit F hF H'.lies (u i) e (x i) (fun j=> B j i) hi hs (h'.trans hb) (fun j k hk=>hL.trans_le (hV.ways hk)) (fun (_:Unit) (j:J)=>by simpa only [zero_sub,norm_neg,sub_zero] using hB.trans_le (hV.outside j)) hI hQ (fun j=> hY.budget (e j) (hw j)) (k i)

-- Now mesh configuration creation & price. Need choose estimator heights K (t at ε, common Stall) and m (from
-- R at `↑ ε`, choose below t and avoid overshooting true scale so hT etc).
omit hp he hR hy hA
variable {W r D} (hL:LogPackage C W r D)
variable (d':I→ℕ)
local notation "κ'"=> C.path.levels
variable (hr:Ridge l T g)(hK:∀ᶠ i in l, Shelf (g i) (R i) (t i))
variable (hZ:RateIs l T (fun i=> t i / R i) a)(hY:RateIs l T (fun i=> R i/g i) b)

include hK
omit H H' hT
lemma shelfSize : ∀ᶠ i in l,R i∈ Ioc (0:ℝ) 1:= hK.mono fun _ hi=>⟨hi.period.2.1,hi.tie.2.trans hi.stop⟩
lemma shelf_upper : ∀ᶠ i in l,t i∈ Ioc (0:ℝ) 1:= hK.mono fun _ hi=>hi.period.2.2
lemma shelf_down : ∀ᶠ i in l,g i ≤ t i:= hK.mono fun _ hi=>hi.fit.trans hi.tie.2
include hT H H' hL hZ hY hr
variable (hx:Ridge l T t)
variable (ha:a> 2*ε)(he':ε>0)(hb:b≥0)
include hx ha he' hb

/-- enough space for an entire crew. Use κ comparison with slightly higher QC rank to purchase
    independent margins even for biggest weights on this same script. -/
structure Promissory (𝓛:Ultrafilter (ℕ×ℕ))(S:Table C.book)(T g t R:V→ℝ)(j m q:V→ℕ)(l:Filter V)(G Z:V→ℝ)(v:V→I→ S.Tag)(d:ℕ) :Prop where
   offers : ∀ x: V→ I→ Cover, (∀ᶠ i in l, VisitS (g i) (R i) (C.S.gridPoint (j i) ∘ x i) 0) → ∀ᶠ i in l, ∃ y, Stall (C:=C) 𝓛 S (q i) (m i) (j i) (G i) (Z i) d (x i) (v i) y

-- use ∀x inside eventually since operators may normalize grid to varying origin.
-- Burn exactly these floors. hQ chosen depends on overshoot.
set_option maxHeartbeats 650000 in
lemma purchase_margins [DecidableEq I] (V':I)(hD : Dusk.Shipper C.path r D) (hW:Dusk.Feasible C.path.levels)(H₀:Stock.Tabs C.path.levels)
    (c:ℝ)(hE: (4*n':ℕ)*(b+2*ε)+ (∑ i, (d' i + 2:ℝ)*ε) -((d:ℝ)+1/8)*(a-2*ε)<c) :
    ∃ (q m j: V→ℕ) (o C':V→ℝ), Layer C l T q ∧ RateIs l T (fun i=> t i/α! (q i)) ε ∧ Layer C l T j ∧ RateIs l T (fun i=> g i/α! (j i)) ε ∧
    RateLE l T o c ∧ ∀ᶠ i in l,(q i ≤ j i ∧ ∀ (x:I→ Cover),VisitS (g i) (R i) (C.S.gridPoint (j i) ∘ x) 0 → ∀ v:∀ k:I, S.Field (d' k), (∀ w, cost F (d' w) (g i) (v w)≤1) →∃ z:S.Field d, Stall (C:=C) 𝓛 S (q i) (m i) (j i) (o i) (C' i) d x (fun j=>⟨d' j,v j⟩) z):=by
   -- pick δ below log-t by ε. pick m below t by (a-ε), so ∼ R*exp(e*T)
   have ha':a-ε>0:=by linarith
   let y:=plunge t ε T; let p:=plunge t (a-ε) T; let x:=plunge g ε T; have hY':= hx.motion hT he'; have hf:=hx.motion hT ha'; have hv:=hr.motion hT he'
   obtain ⟨w',hw⟩:= price_tall d'
   obtain ⟨q,-,A',hQ,-,ht,-,-,-⟩:= locate hT F hG H' 0 hY'.1 hY'.2.1
   obtain ⟨m,-,R',hm,-,hh,-,-,-⟩:= locate hT F hG H' 0 hf.1 hf.2.1
   obtain ⟨j,l',B,hj,-,hJ,-,hB,hP⟩:= locate hT F hG H' w' hv.1 hv.2.1
   let b'(v:I)(i:V):=Real.exp ((d' v+2:ℝ)*ε*T i); let e(v:I):ℝ:=(d' v+2:ℝ)*ε; have he(v:I):RateIs l T (b' v) (e v):=RateIs.exp _ hT
   have hU:RateIs l T (fun i=> t i/C.S.a (q i)) ε:= (relation_mul (hY'.1.pos.mono fun i hi=>hi.ne') hY'.2.2.2 (relation_inv ht)).swap (by simp)
   have hT':RateIs l T (fun i=> t i/C.S.a (m i)) (a-ε):=(relation_mul (hf.1.pos.mono fun i hi=>hi.ne') hf.2.2.2 (relation_inv hh)).swap (by simp)
   have hz:RateIs l T (fun i=> g i/C.S.a (j i)) ε:= (relation_mul (hv.1.pos.mono fun i hi=>hi.ne') hv.2.2.2 (relation_inv hJ)).swap (by simp)
   have hy: RateIs l T (fun i=> α! (q i)/α! (m i)) (a-2*ε):= (relation_mul (hx.pos.mono fun i hi=>hi.ne') (relation_inv hU) hT').swap (by ring)
   have hR: RateIs l T (fun i=> α! (m i)/ R i) ε:= (relation_mul (hx.pos.mono fun i hi=>hi.ne') (relation_inv hT') hZ).swap (by ring)
   have hJ:RateIs l T (fun i=> α! (m i)/ α! (j i)) (b+2*ε):=(relation_mul ((shelfSize hK).mono fun i hi=>hi.1.ne') hR (relation_mul (hr.pos.mono fun i hi=>hi.ne') hY hz)).swap (by ring)
   have hM:0< b+2*ε:=(by linarith); obtain ⟨o,V₀,hk,h₀⟩:= expense_grid hT hG H'.budgets hL hQ hm hy (sub_pos.mpr ha) f F d' hD hW H₀ d V' hj hM hJ b' e he c hE
   refine ⟨q,m,j,o,V₀,hQ,hU,hj,hz,hk,?_⟩
   have he₁:= tower_earlier hT hy (sub_pos.mpr ha); have hm':= hm.jump hT hL
   have hf: RateIs l T (fun i=>α! (m i+1)/R i) ε:= (relation_mul (Eventually.of_forall (fun i=> (C.S.a_pos (m i)).ne')) (relation_inv hm') hR).swap (by simp)
   have h₂ := tower_earlier hT (tower_attach hJ (relation_inv hm')) (by simpa using hM)
   choose A hA using fun (i:I)=> token_grants F H (d' i) 1 one_pos
   have hh(w:I) : ∀ᶠ i in l,(B i)*(A w*(g i/ (x i))^((d' w:ℝ)+1)) ≤ b' w i:=by
      refine ((he w).overtakes ((hB.mul ((RateIs.const hT (zero_lt_one.trans_le (hA w).budget)).mul (hv.2.2.2.rpow ((d' w:ℝ)+1)))).pays hT) hT (by unfold e; linarith only [he'])).mono fun i hi=> hi.le
   let Y i:ℝ := ((C.path.levels.budget (j i)).B:ℝ)
   have hY' : RateLE l T Y 0:= hj.cover hT
   filter_upwards [h₀,he₁,h₂,hP,eventually_all.mpr hh,hK,hv.2.2.1,hv.1.pos,hB.pos,tidal hT hf he' ((shelfSize hK).mono fun i h=> h.1) 16,hz.overtakes ((RateLE.const (4:ℝ) hT).mul (hY'.pow 2 hT)) hT (by simpa using he')] with i hf he hm ht hQ hK hx hG hh hr hz
   have hk:q i ≤ m i:= he.le; have hr':m i+1 ≤ j i:= hm.le
   refine ⟨hk.trans ((m i).le_succ.trans hr'),fun y hy v hν=> ?_⟩
   refine stall_create F (B i) (q i) (m i) (j i) (l' i) d (plunge g ε T i) d' y v _ _ (fun w=> _) (fun w=> ht.budget _ (hw w)) ?_ hf ?_ H'.lies -- hd order
   · refine ⟨fun j'=>?_,fun s u hu=>?_,hk,hr'⟩
     · have he: ‖C.S.gridPoint (j i) (y j')‖ ≤ 2*R i:=(by simpa only [sub_zero,Function.comp_apply] using hy.admits j'); linarith only [he,hr]
     have ha:= (lt_div_iff₀ (C.S.a_pos _)).1 (show 4*(Y i)^2 < g i/C.S.a (j i) from hz); change 2*C.S.a (j i)*Y i^2 < _; linarith only [ha,hy.shares hu]
   intro w; have he: cost F (d' w) (x i) (v w) ≤ A w*(g i/x i)^((d' w:ℝ)+1)*1:=( (hA w).left (show g i∈ Ioc (0:ℝ) 1 from ⟨hK.credit,(hK.fit.trans hK.tie.2).trans hK.stop⟩) (show x i∈ Ioc 0 (g i) from ⟨hG,hx⟩) _).trans (mul_le_mul_of_nonneg_left (hν w) (by change 0 ≤ A w*_; exact mul_nonneg (zero_le_one.trans (hA w).budget) (Real.rpow_nonneg (div_pos hK.credit hG|>.le) _)))
   rw [mul_one] at he; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left he hh.le).trans (hQ w)) (pow_nonneg (C.S.a_pos _).le _)
end YM.GapsContact.Seams
