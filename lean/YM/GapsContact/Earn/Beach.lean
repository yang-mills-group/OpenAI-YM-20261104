import YM.GapsContact.BudgetCheckpoint
import YM.OPE.Coverage.Temporal

/-!
# Raw words with individual priced timestamp clearances

On the chamber & spread that price slab. Supports the distinguished representatives exposed to
`Small.bar`, no cutoff cost on lifts. (Grid calls later purchase `Vane` receipts separately.)

Any positions with the clearances, with RELATIVELY SMALL widths, use exact p-slabs. Factorization
uses Euclidean product already at this P and rotation-changed points, not changing any real-time
contour choice. Proof components adapted from Coverage.Sailing (uses Fare, a condition on token
lifts in *every* chamber Hilbertization); instead here need only `P`'s centered estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Ward Spec Table OS OS.Ground OS.Semigroup Word Climb
open Ascent Power
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Classical

variable {G:Gauge}
section Hilbert
variable {L:Register G}{S:Table L}(V:Chamber S timeAxis)(P:Spread V){d:ℝ≥0}{w:L.Word}
local notation "Q" => basis timeAxis
lemma bank_shift (h:Slab timeAxis d w)(u r:ℝ≥0):
   ‖P.place (u+d+r) (raised timeAxis u w)‖ ≤ ‖P.place d w‖:=by
   rw [stretches P (fills h u), crossing P h]
   apply le_trans (ContinuousLinearMap.opNorm_comp_le ..)
   apply (mul_le_of_le_one_right (norm_nonneg _) (V.flow.shrinks _)).trans; exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (V.flow.shrinks _))
lemma bank_move (h:Slab timeAxis d w)(t:E4)(ht:t timeAxis=0) :
   ‖P.place d (carry w t)‖ ≤ ‖P.place d w‖:=by
   let s:Cross timeAxis := ⟨t,ht⟩
   refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x=> ?_
   let y:=V.flow.U (-s) x; have he: V.flow.U s y=x:=by unfold y; rw [← ContinuousLinearMap.comp_apply, ← V.flow.space, add_neg_cancel, V.flow.uZero]; rfl
   rw [← he,← ContinuousLinearMap.comp_apply, ←P.perpendicular h s, ContinuousLinearMap.comp_apply,V.flow.unitary,V.flow.unitary]; exact ContinuousLinearMap.le_opNorm ..
local notation "σ" => Work.C01.center
lemma bank_slot (e : ℝ≥0) (v : L.Token) {p : ℝ≥0} (hp : 0 < p) (x : E4) (hr:(p:ℝ) ≤ x timeAxis) (hf:x timeAxis+(p:ℝ) ≤ e) :
   ‖P.place e ([(x,v)]:L.Word)‖ ≤ ‖P.place (p+p) [σ p v]‖:=by
   let u:ℝ≥0 := ⟨x timeAxis-p,sub_nonneg.mpr hr⟩; let a:=u+(p+p); have hu:(u:ℝ)=x timeAxis-p:=rfl
   have ha:a ≤ e:=by change (a:ℝ) ≤ e; unfold a; push_cast; linarith only [hf, hu]
   let t:=x-position 0 p-(u:ℝ) • basis timeAxis; let v':=(σ p v); let w':= raised timeAxis u [v']
   have ht:t timeAxis=0:=by unfold t; simp only [PiLp.sub_apply,PiLp.smul_apply]; rw [show position (0:Space3) (p:ℝ) timeAxis=(p:ℝ) from time_position _ _,hu]; simp
   rw [show [(x,v)]= carry w' t from ?_]; swap
   · unfold w' t v' Work.C01.center raised carry; simp only [List.map_cons,List.map_nil]; congr 2; ext
     -- addition
     simp only [PiLp.add_apply, PiLp.sub_apply]; ring
   obtain ⟨r,hr⟩:= exists_add_of_le ha; subst e; refine (bank_move V P (swelling (fills (Work.C01.centeredSlab p v hp) u) r) t ht).trans ?_; exact bank_shift V P (Work.C01.centeredSlab p v hp) u r

/-- ticket centered cost. -/
abbrev Bucc (p:ℝ≥0)(k:L.Token):ℝ:=‖P.place (p+p) [σ p k]‖

set_option maxHeartbeats 750000 in
lemma plank (w:L.Word) (b:L.Plant→ℝ≥0) (hb : ∀ i∈w,0<b i) (H : S.Hierarchy)
     (ha:∀ x∈w, (b x:ℝ) < x.1 timeAxis) (h:w.Pairwise (fun x y=> x.1 timeAxis + (b x:ℝ) + (b y:ℝ) < y.1 timeAxis)) :
         ∃ f:Future L timeAxis,f.val = w ∧ ‖V.GNS.plant f‖ ≤ (w.map fun x=> Bucc V P (b x) x.2).prod:= by
   match w with
   | [] => exact ⟨air timeAxis,rfl,(OS.nil_norm _ H.laws).le⟩
   | x::w =>
        obtain ⟨hx,h⟩:= List.pairwise_cons.mp h
        have he:=ha x List.mem_cons_self; have hv:=hb x List.mem_cons_self
        let d:ℝ≥0:=⟨x.1 timeAxis + (b x:ℝ), (by linarith only [he,show (0:ℝ)<b x from hv])⟩
        have hd:(d:ℝ)=x.1 timeAxis + (b x:ℝ):=rfl
        have hu : Slab timeAxis d ([x]:L.Word) := by
           constructor
           · change 0<(d:ℝ); linarith only [he,hd,show (0:ℝ)<b x from hv]
           constructor
           · exact ⟨locations.mpr (by simp),fun y hy=> (List.mem_singleton.mp hy).symm ▸ (lt_trans (show (0:ℝ)<b x from hv) he)⟩
           exact fun y hy=> (List.mem_singleton.mp hy).symm ▸ lt_add_of_pos_right _ (show (0:ℝ) < b x from hv)
        let back (y:L.Plant) : L.Plant := (y.1-(d:ℝ) • basis timeAxis,y.2)

        let ahead (y:L.Plant):L.Plant:= (y.1+(d:ℝ) • basis timeAxis,y.2)
        have heq (y:L.Plant): ahead (back y)=y:=by simp [ahead,back]
        have atBrush (y:L.Plant) : (back y).1 timeAxis = y.1 timeAxis -(d:ℝ) := by change (y.1-(d:ℝ) • _) _ = _; simp
        have hi₀ : ∀ x'∈w.map back, 0 < (b∘ahead) x' := by rintro z hz; obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hz; rw [Function.comp_apply,heq]; exact hb y (List.mem_cons_of_mem _ hy)
        have hA : ∀ x'∈w.map back, ((b∘ahead) x' : ℝ) < x'.1 timeAxis:=by
           intro _ h'; obtain ⟨y,hy,rfl⟩:= List.mem_map.mp h';rw [atBrush,Function.comp_apply,heq]; linarith only [hd,hx y hy]
        have hPairs: (w.map back).Pairwise (fun x y=> x.1 timeAxis+((b∘ahead) x:ℝ)+((b∘ahead) y:ℝ)<y.1 timeAxis):= by
           rw [List.pairwise_map]; simp_rw [atBrush,Function.comp_apply,heq]; exact h.imp fun hl=>by linarith
        obtain ⟨f,hF,h_f⟩:= plank (w.map back) (b ∘ ahead) hi₀ H hA hPairs
        refine ⟨entering hu f,?_,?_⟩
        · change [x] ++ raised timeAxis d f.val=_; rw [hF]
          simp [raised, carry, back, List.map_map,Function.comp_def]
        rw [← P.reads hu]; apply ((ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (bank_slot V P d x.2 hv x.1 he.le (le_of_eq hd.symm)) h_f (norm_nonneg _) (norm_nonneg _))).trans_eq
        simp_rw [Bucc,List.map_cons,List.map_map,Function.comp_def,heq,List.prod_cons]; rfl
termination_by w.length

lemma shore_sorted (w:L.Word) (H:S.Hierarchy) (b:L.Plant→ℝ≥0) (hb:∀ v∈w,0<b v)
     (hp:w.Pairwise (fun x y=> x.1 timeAxis + (b x:ℝ) + (b y:ℝ) < y.1 timeAxis)) :
          ‖S.expect w‖ ≤ (w.map fun x=> Bucc V P (b x) x.2).prod:= by
    obtain ⟨c,h⟩ : ∃ M:ℝ, ∀ x∈w, (b x:ℝ)-x.1 timeAxis < M := by simpa using (eventually_all_finset w.toFinset |>.mpr fun x _=> (eventually_gt_atTop ((b x:ℝ) -x.1 timeAxis))).exists
    let v(x:L.Plant):L.Plant:= (x.1+c • basis timeAxis,x.2); let u(x:L.Plant):L.Plant:= (x.1-c • basis timeAxis,x.2)
    have he(x:L.Plant): u (v x)=x:=by simp[v,u]
    have hf(x:L.Plant) : (v x).1 timeAxis=x.1 timeAxis + c:=by unfold v;simp
    obtain ⟨p,hp',hw⟩:= plank V P (w.map v) (b ∘ u) (by rintro w hi; obtain ⟨x,hx,rfl⟩:= List.mem_map.mp hi; rw [Function.comp_apply,he]; exact hb x hx) H (by rintro w hi; obtain ⟨x,hx,rfl⟩:= List.mem_map.mp hi; rw [Function.comp_apply,he,hf]; linarith only [h x hx]) (by rw [List.pairwise_map]; simp_rw [Function.comp_apply,he,hf]; exact hp.imp fun hf=>by linarith)
    have hc: Word.distinct w:=by
       apply locations.mpr; rw [List.Nodup,List.pairwise_map]; refine List.Pairwise.imp_of_mem ?_ hp; rintro x y hx hy ht he0; rw [he0] at ht; linarith only [ht, (b x).coe_nonneg,(b y).coe_nonneg]
    rw [show S.expect w= inner ℂ (V.GNS.plant (air timeAxis)) (V.GNS.plant p) from ?_]; swap
    · rw [V.GNS.measure,Table.gram,hp',← invariance H.translations hc (c • basis timeAxis)]; rfl
    refine (norm_inner_le_norm ..).trans ?_; rw [OS.nil_norm V.GNS H.laws,one_mul]; simp only [List.map_map, Function.comp_def,he] at hw; exact hw

lemma shore_price (w:L.Word) (H:S.Hierarchy) (b:L.Plant→ℝ≥0) (hb:∀ v∈w,0<b v)
    (h:w.Pairwise (fun x y => (b x:ℝ)+(b y:ℝ)< |x.1 timeAxis-y.1 timeAxis|)) :
         ‖S.expect w‖ ≤ (w.map fun x=> Bucc V P (b x) x.2).prod:= by
   let R(x y:L.Plant):Prop:= x.1 timeAxis≤ y.1 timeAxis
   let K(x y:L.Plant): Bool := decide (R x y)
   let tie(x y:L.Plant):Prop:= (b x:ℝ)+(b y:ℝ)< |x.1 timeAxis-y.1 timeAxis|
   let w':= w.mergeSort K
   have he : w'.Pairwise R:= by
      simpa only [w',K,decide_eq_true_eq] using List.pairwise_mergeSort (le:=K) (by simp [K,R]; exact fun a b c=> le_trans) (by simp [K,R,le_total]) w
   have hp:= List.mergeSort_perm w K
   have ht : w'.Pairwise tie:= hp.symm.pairwise h (fun {i j} ht=> by unfold tie at *; rw [abs_sub_comm,add_comm]; exact ht)
   refine le_trans ?_ (le_of_eq ((hp.map (fun x=>Bucc V P (b x) x.2)).prod_eq))
   have hc : distinct w:=by
       apply locations.mpr; rw [List.Nodup,List.pairwise_map]; refine List.Pairwise.imp_of_mem ?_ h; rintro x y hx hy h he; rw [he,sub_self,abs_zero] at h; linarith only [h,(b x).coe_nonneg,(b y).coe_nonneg]
   rw [← S.order H.laws.toSymmetric hc hp.symm] -- order
   apply shore_sorted V P w' H b (fun x hx=>hb x (hp.mem_iff.mp hx)); refine List.Pairwise.imp ?_ (he.and ht); rintro x y ⟨he,h⟩; unfold tie at h; rw [abs_of_nonpos (sub_nonpos.mpr he)] at h; linarith only [h]

variable {n:ℕ}
lemma raw_window (v:Fin n→L.Token)(x:Points n)(H:S.Hierarchy) (p:Fin n→ℝ≥0) (hp:∀i,0<p i)
   (ht:Pairwise (fun i j=> (p i:ℝ)+(p j:ℝ)< |x i timeAxis-x j timeAxis|)) :
   ‖S.read x v‖ ≤ ∏ i, Bucc V P (p i) (v i) :=by
   have he: Injective x.ofLp:= fun i j hij=> by by_contra! hc; have hh:=ht hc; dsimp only at hh; rw [hij,sub_self,abs_zero] at hh; linarith only [hh,(p i).coe_nonneg,(p j).coe_nonneg]
   let g(i:Fin n):L.Plant:=(x i, v i); have hu:Injective g := fun i j hij=> he (Prod.mk.inj hij).1
   let b:= extend g p (fun _=>0); let w:= Word.realize v x
   have hh(i): b (g i)=p i:= hu.extend_apply ..
   rw [←S.readAt]
   refine (shore_price V P w H b ?_ ?_).trans_eq ?_
   · rintro y hy; obtain ⟨k,rfl⟩:=List.mem_ofFn.mp (show y∈List.ofFn g from hy); rw [hh]; exact hp _
   · rw [show w=List.ofFn g from rfl,List.pairwise_ofFn]; intro i j hij; rw [hh,hh]; exact ht hij.ne
   simp only [w,realize,List.map_ofFn,Fin.prod_ofFn]; exact Finset.prod_congr rfl fun i _=> congr_arg (fun p=> Bucc V P p (v i)) (hh i)
end Hilbert

variable {n:ℕ} {d:Fin n→ℕ}
variable {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(L:EveryPhase.Almanac F)
open Ascent.Survey Trace Trace.Pilot
universe u
include L
lemma region (v:∀i,S.Field (d i))(x:Points n) (s: Survey F) (p:Fin n→ℝ≥0) (hp:∀i,0<p i)
   (ht:Pairwise (fun i j=> (p i:ℝ)+(p j:ℝ)< |x i timeAxis-x j timeAxis|)) :
   ‖S.useAt (Survey.table s) x (fun i=> (⟨d i,v i⟩:S.Tag))‖ ≤ ∏ i, ‖Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric (hp i) (d i) (v i)‖ := by
   let w(i):=(⟨d i,S.representative _ (v i)⟩:C.book.Token)
   have he : S.useAt (Survey.table s) x (fun i=> (⟨d i,v i⟩:S.Tag)) = (Survey.table s).read x w:= rfl
   rw [he]
   refine (raw_window (chamber L s) (spread L s) w x (pantry L s).adopted p hp ht).trans ?_; apply Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>?_) ; exact Survey.uniform L s _ (hp j) (d j) (v j)

lemma beach_oriented (v:∀i,S.Field (d i))(x:Points n) (s: Survey F) (p: Fin n→ℝ≥0) (A μ r δ:Fin n→ℝ) (m:Fin n→ℕ) (K:Ortho) (he:x∈conf n) (hp:∀i,0<p i)
   (hd:∀i,δ i∈Ioc (0:ℝ) 1) (hr:∀i,r i∈Ioc 0 (μ i)) (hA:∀i,1≤A i) (hh:∀i,r i*δ i≤p i) (hF:∀i,OpenSky F (d i) (μ i) (A i) (m i))
   (ht:Pairwise (fun i j=> (p i:ℝ)+(p j:ℝ)< |Ortho.move K (x i) timeAxis-Ortho.move K (x j) timeAxis|)) :
   ‖S.useAt (Survey.table s) x (fun i=> (⟨d i,v i⟩:S.Tag))‖ ≤ ∏ i, A i^2 * (LogV (r i) / δ i)^(2*m i)*cost F (d i) (r i) (F.sector.turns.act _ K (v i)) := by
   have hX : F.sector.turns.Oriented (Survey.table s) := by
      cases s with
      | some i=> exact F.phase.phase.sym i
      | none => exact F.phase.transport.motion
   rw [← hX n _ x he K]; let w(i):= F.sector.turns.act _ K (v i); apply (region F L w _ s p hp ht).trans ?_; apply Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=>?_)
   exact own_pay F (hF j).archive (hA j) (hr j) (hd j) ((hF j).duration (r j) (hr j)) (p j) (hp j) (hh j) (w j)

omit L
open Trace.Terrace Trace.Over Next.UVStress MergeProof.East Work.A05 Spin
lemma smallEstate {p:ℝ→Prop}(h: ∀ᶠ r in trail,p r): ∃ R₀:ℝ,0<R₀ ∧∀ r∈Ioc 0 R₀,p r:=by
   rw [eventually_nhdsWithin_iff] at h
   obtain ⟨r,hr,hR⟩:= Metric.eventually_nhds_iff.mp h
   exact ⟨r/2,half_pos hr,fun s hs=> hR (by rw [Real.dist_eq,sub_zero,abs_of_pos hs.1]; exact hs.2.trans_lt (half_lt_self hr)) hs.1⟩

lemma eventuallyTrial {p: ℝ→ℝ→Prop} {𝓛: Ultrafilter (ℕ × ℕ)} {Z:Trace.Terrace.Arch C}{H:(Climb.Bel C.book).Hierarchy} (hX:Bliss F 𝓛 Z H) (he:∀ r a b,a ≤ b→ p r a→ p r b)
       (hx:∀ {J:Scaling S} {V:∀ i,Vane C i}, Scribe f J V Z F.sector 𝓛 F.room.kernel H →∃ A:ℝ,∀ᶠ i in atTop,p (J.r i) A) : ∃ A:ℝ,1≤A ∧∀ᶠ r in trail,p r A:=by
   by_contra! h
   have hw(i:ℕ):∃ s:ℝ,0<s ∧ s<costHint i ∧ ¬ p s (sizeHint i) :=by
     obtain ⟨s,h,h1,h2⟩:= ((h (sizeHint i) (by unfold sizeHint; simp)).and_eventually ((show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).and ((gt_mem_nhds (Next.UVStress.cost_pos i)).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨s,h1,h2,h⟩
   choose s h h' hg using hw
   obtain ⟨m,hm,J,hJ,V,hV⟩:= hX.picks s (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun i=> (h i).le) (fun i=>(h' i).le)) h
   obtain ⟨B,hK⟩:= hx hV
   obtain ⟨i,hi,hp⟩:= (hK.and ((size_ascends.comp hm.tendsto_atTop).eventually_ge_atTop B)).exists
   rw [hJ] at hi; exact hg (m i) (he _ _ _ hp hi)

variable {hG:G.Simple}(T:Roll.{u} F hG L)
include T L
attribute [local instance] Work.A15.compact_ortho
lemma tornado (d:ℕ) :∃ B:ℝ,1≤ B ∧ ∀ᶠ r in trail,∀ (g:Ortho) (x:S.Field d), cost F d r (F.sector.turns.act d g x) ≤ B * cost F d r x := by
   obtain ⟨H,W,ℓ,hU,-,-⟩:=T.trace.stress
   obtain ⟨B,hB,h⟩:= Jost.have_stable F hG hU d
   let V:=circle (compass (C:=C) (H:=H) hG) (LinearEquiv.refl ℂ ((Bel C.book).Field d)); have hv:= circle_cont (compass (C:=C) (H:=H) hG) (LinearEquiv.refl ℂ ((Bel C.book).Field d))
   obtain ⟨g₀,-,hg⟩:=isCompact_univ.exists_isMaxOn univ_nonempty hv.norm.continuousOn
   let D:=max 1 ‖V g₀‖; have hd:1≤D:= le_max_left ..
   have hz(g:Ortho): ‖V g‖≤D:= (hg (Set.mem_univ _)).trans (le_max_right ..)
   refine ⟨B*(D*B),one_le_mul_of_one_le_of_one_le hB (one_le_mul_of_one_le_of_one_le hd hB),?_⟩
   filter_upwards [h] with r ⟨R,hR⟩ g x
   obtain ⟨v,rfl⟩:= R.surjective x
   rw [← hR.align.axis]; refine (hR.budget (V g v)).trans ?_; simp only [mul_assoc]; gcongr
   exact ((V g).le_opNorm v).trans ((mul_le_mul (hz g) (hR.inverse v) (norm_nonneg _) (zero_le_one.trans hd)))

lemma spin_flight (d:ℕ) : ∃ B:ℝ,1≤B ∧∀ᶠ r in trail,∀ x:S.Field d,cost F d r (flipField F d x)≤ B*cost F d r x:=by
   -- conjugation moves via leading path. not claiming law equality of `cost` on spin.
   obtain ⟨H,Z,ℓ,hU,-,-⟩:=T.trace.stress
   refine eventuallyTrial F (p:=fun r B=>∀ x:S.Field d, cost F d r (flipField F d x) ≤ B*cost F d r x) hU (fun r a b hr hh x=> (hh x).trans (mul_le_mul_of_nonneg_right hr (Ascent.cost_pos ..))) ?_ -- argument placeholders
   intro J V hJ
   let h:=hJ.monorail
   obtain ⟨B,hB,hY⟩:= window_prices F hG h d 1 1 one_pos
   let f:((Bel C.book).Field d) →ₛₗ[starRingEnd ℂ] ((Bel C.book).Field d):=(Bel C.book).adj H.spin d timeAxis
   let t:(Bel C.book).Field d →ₗ[ℝ] (Bel C.book).Field d := { toFun := f, map_add':= f.map_add, map_smul' := fun c v=> (by rw [←Complex.coe_smul,← Complex.coe_smul, LinearMap.map_smulₛₗ]; simp) }; letI : FiniteDimensional ℝ ((Bel C.book).Field d) := Module.Finite.trans ℂ _
   let M:=max 1 ‖LinearMap.toContinuousLinearMap t‖
   have hx: ∀ v:(Bel C.book).Field d, ‖f v‖ ≤ M*‖v‖:= fun x=> ( (LinearMap.toContinuousLinearMap t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)) -- might require proof trans semi-linear finite
   have hp: 1≤M:= le_max_left ..
   refine ⟨B*(M*B),?_⟩
   filter_upwards [hY,h.units d] with i hi hv x
   obtain ⟨t,rfl⟩:= (J.U i d).surjective x; obtain ⟨hL,-⟩:=hv
   change cost F d (J.r i) (S.mirror _ _ _ (S.conj _ _ (J.U i d t))) ≤ _; rw [← hL.stars,← hL.signed]
   have hh : cost F d (J.r i) (J.U i d (f t)) ≤ B*‖f t‖:=by simpa only [mul_one] using (hi (f t)).2 1 ⟨le_rfl,le_rfl⟩
   apply hh.trans; simp only [mul_assoc]; exact mul_le_mul_of_nonneg_left ((hx t).trans (mul_le_mul_of_nonneg_left (hi t).1 (zero_le_one.trans hp))) (zero_le_one.trans hB)

lemma starlight (d:ℕ)(a:Axis) : ∃ B:ℝ,1≤ B ∧ ∀ᶠ r in trail,∀ x:S.Field d,cost F (d+1) r (r • F.sector.derivatives.deriv d a x) ≤ B*cost F d r x :=by
    obtain ⟨H,Z,ℓ,hU,-,-⟩:=T.trace.stress; refine eventuallyTrial F (p:=fun r B=>∀ x:S.Field d, cost F (d+1) r (r • F.sector.derivatives.deriv d a x) ≤ B*cost F d r x) hU (fun r a b hr hx x=> (hx x).trans (mul_le_mul_of_nonneg_right hr (Ascent.cost_pos ..))) ?_
    intro J V hJ
    let Q(i:ℕ):= tiltScale J F.sector.derivatives i d a
    let L:=leaves (Maxwell.Free.scheme C.labels).deriv d a
    have ht:Tendsto Q atTop (𝓝 L):= bend_limit F.room.kernel F.phase.transport.derivatives H (Maxwell.Free.scheme_derives _) J d a hJ.monorail.approach
    obtain ⟨B,hB,hY⟩:= window_prices F hG hJ.monorail d 1 1 one_pos; obtain ⟨A,hA,hE⟩:= window_prices F hG hJ.monorail (d+1) 1 1 one_pos
    let c:= ‖L‖+1; have hp:0<c:=by unfold c; positivity
    refine ⟨A*(c*B),?_⟩
    filter_upwards [hY,hE,ht.eventually ((show ContinuousAt (fun T: (Bel C.book).Field d→L[ℂ] (Bel C.book).Field (d+1)=>‖T‖) L from (continuous_norm (E:= (Bel C.book).Field d →L[ℂ] (Bel C.book).Field (d+1))).continuousAt).eventually (ge_mem_nhds (show ‖L‖<c from lt_add_one ..)))] with i hx he hv x
    obtain ⟨t,rfl⟩:= (J.U i d).surjective x
    have hw : J.U i (d+1) (Q i t)= J.r i • (F.sector.derivatives.deriv d a (J.U i d t)):=by
       let A:= J.carry i (leaves F.sector.derivatives.deriv d a) t; have hd := ((J.U i (d+1)).toLinearMap.restrictScalars ℝ).map_smul (J.r i) A
       change J.U i (d+1) (J.r i • A)= _; refine hd.trans ?_; change (J.r i • J.U i (d+1) A)=_; exact congr_arg _ (J.carries_f ..)
    rw [← hw]; have hT : cost F (d+1) (J.r i) (J.U i (d+1) (Q i t)) ≤ A*‖Q i t‖:=by simpa only [mul_one] using (he (Q i t)).2 1 ⟨le_rfl,le_rfl⟩
    apply hT.trans; simp only [mul_assoc]; exact mul_le_mul_of_nonneg_left (((Q i).le_opNorm t).trans (mul_le_mul hv (hx t).1 (norm_nonneg _) hp.le)) (zero_le_one.trans hA)

end YM.GapsContact.Seams
