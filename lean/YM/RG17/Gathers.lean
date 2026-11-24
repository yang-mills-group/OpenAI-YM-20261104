import YM.RG17.Cord

/-!
# Reading at actual UV+period cutoffs

Absolute stencil positions, physical ensemble. All grades on their
actual calibrated charts, `i : UVIndex` always cutoff,period order.
Expanding pivots in FULL letter probes across all their reporting
heights. Using the all-r reporting language for now (L.shift may
include perturbative calibration convention). Before attempting physics
claims, prove representation and budget estimates on these readouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Extraction Table OPE OPE.Orbits RG12
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Spec.Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S)
    (L:Layout F) (loc:Located L) (X: External C S) {n:ℕ}
    {r:ℝ}{D:ℕ}{d e:Fin n→ℕ}

-- actual fixed-entry coordinates. Don't forget factors converting
-- k-caps, basis shifts and engineering units.
def atRef (L:Layout F)(D:ℕ)(r:ℝ) (i:UVIndex)(x:C.label D) : C.label D :=
   (↑(C.S.a (L.level r)^D):ℂ) • atK C F.room.cutoff D (L.level r) i (L.shift D r x)
def locatedRef (L:Layout F)(D:ℕ)(r:ℝ)(x:C.label D) : C.label D :=
   (↑(C.S.a (L.level r)^D):ℂ) • L.charts D (L.level r) (L.shift D r x)

lemma payRef (x:C.label D) : S.project D (locatedRef L D r x)= master L D r x :=by rw [locatedRef,map_smul]; rfl
lemma tendsRef {x:C.label D} {v:UVIndex→ C.label D} {u:Filter UVIndex} [u.NeBot] (he:u ≤ L.lens) (hp:Tendsto v u (𝓝 x)) (h:C.ref D ≤ L.level r):
    Tendsto (fun i=>atRef L D r i (v i)) u (𝓝 (locatedRef L D r x)):=by
   let j:= fun p: RepChart C D × C.label D=> p.1 p.2
   have hy:Continuous j:= continuous_fst.clm_apply continuous_snd
   have hk := L.observes.tends D (L.level r) h
   have hv:= ((L.shift D r).continuous_of_finiteDimensional.continuousAt (x:=x)).tendsto.comp hp
   exact tendsto_const_nhds.smul ((hy.tendsto _).comp (((hk.mono_left he)).prodMk_nhds hv))

abbrev refTags (X: External C S) := names X.labels

def packMark (L:Layout F)(X:External C S)(e:Fin n→ℕ) (v:(j:Fin n)→ C.label (e j))(r:ℝ)(ψ:Test n)(i:UVIndex):ℂ:=
    Order.smears C i.1 i.2 (Fin.append (fun j=> ⟨e j,atRef L (e j) r i (v j)⟩) (refTags X)) (shape X r ψ)
def headMark (L:Layout F)(X:External C S)(D:ℕ)(r:ℝ)(i:UVIndex)(x:C.label D):ℂ:=
    Order.smears C i.1 i.2 (Fin.cons ⟨D,atRef L D r i x⟩ (refTags X)) X.test

def joinRef {k:ℕ}{e:Fin k→ℕ}(C:Family G)(d:Fin n→ℕ)(t:(i:Fin n)→ C.label (d i))(u:(i:Fin k)→C.label (e i))(i:Fin (n+k)):
   C.label (Fin.append d e i) := Fin.addCases (fun a:Fin n=> (Fin.append_left ..) ▸ t a) (fun a:Fin k=> (Fin.append_right ..) ▸ u a) i

private lemma pn (g h:ℕ)(e:g=h)(v:C.label h) : (⟨h,v⟩:C.book.Token)=(⟨g,e.symm ▸ v⟩: C.book.Token):=by subst h; rfl
private lemma shifted {v:UVIndex→ C.label D}{b:Filter UVIndex}{x:C.label D}{k':ℕ}(ht:Tendsto v b (𝓝 x))(e:k'=D) : Tendsto (fun i=> (e.symm ▸ v i:C.label k')) b (𝓝 (e.symm ▸ x:C.label k')):=by subst D; exact ht

lemma pairNames {d:Fin n→ℕ}(v:(i:Fin n)→C.label (d i)) :
    Fin.append (fun i=>(⟨d i,v i⟩:C.book.Token)) (refTags X)=fun i=>(⟨Fin.append d X.degree i,joinRef C d v (fun i=> S.representative (X.degree i) (X.labels i)) i⟩: C.book.Token):=by
    funext i; cases i using Fin.addCases
    all_goals simp only [joinRef,Fin.addCases_left,Fin.addCases_right, Fin.append_left, Fin.append_right]
    · rename_i a; exact pn _ _ (Fin.append_left _ _ a) (v a)
    rename_i b; exact pn _ (X.degree b) (Fin.append_right d X.degree b) (C:=C) (S.representative _ (X.labels b))

lemma limitPack {b:Filter UVIndex}[b.NeBot](he:b ≤ L.lens)(v:(j:Fin n)→ C.label (e j))(ψ:Test n)(hb:∀ i,C.ref (e i) ≤ L.level r) :
    Tendsto (packMark L X e v r ψ) b (𝓝 ((shape X r ψ).applyTo fun y=> S.useAt S y (Fin.append (tags (S:=S) (d:=e) (fun i=> master L (e i) r (v i))) X.tags))) :=by
   have hm(i:Fin n): Tendsto (fun j=> atRef L (e i) r j (v i)) b (𝓝 (locatedRef L (e i) r (v i))) := tendsRef L he (v:=fun _=> v i) tendsto_const_nhds (hb i)
   let w(i:Fin X.n):= S.representative _ (X.labels i)
   let z:= joinRef C e (e:=X.degree) (fun i=> locatedRef L (e i) r (v i)) w
   let t:= (shape X r ψ)
   let p i : C.book.Vector (Fin.append e X.degree) := joinRef C e (fun j=> atRef L (e j) r i (v j)) w
   let g:= Fin.append (tags (S:=S) (d:=e) fun i=>master L _ r (v i)) X.tags
   have hq:= Next.UVStress.calibrated_smear (v:=p) (x:=z) F.room.ordered b (he.trans L.certified) t (he:=fun i=>by
       cases i using Fin.addCases
       · rename_i i
         simp only [p,z,joinRef,Fin.addCases_left]; exact shifted (hm i) (Fin.append_left ..)
       simp only [p,z,joinRef,Fin.addCases_right]; exact tendsto_const_nhds)
   have hc: Fin.append (fun i=> (⟨_,locatedRef L _ r (v i)⟩:C.book.Token)) (refTags X)=fun i=>(⟨_,z i⟩:C.book.Token) := pairNames ..
   have hh: S.integralOn (Fin.append e X.degree) z t= t.applyTo (fun y=>S.useAt S y g):=by
       apply t.apply_eq; intro x hx
       have hA:= (S.at_project S F.room.kernel.laws.toSymmetric (fun _=> le_rfl) hx (fun i=>(⟨_,z i⟩:C.book.Token))).symm
       refine hA.trans (congr_arg (S.useAt S x) ?_); rw [← hc]
       funext i; cases i using Fin.addCases
       all_goals simp only [Function.comp_apply,Fin.append_left,Fin.append_right,g,tags,names]
       · rename_i i; change (⟨e i,S.project _ (locatedRef L _ r (v i))⟩:S.Tag)=_; rw [payRef]
       change (⟨_, S.project _ (S.representative _ _)⟩:S.Tag)=_; rw [S.rep]; rfl
   rw [hh] at hq; exact hq.congr (fun i=> congr_arg (fun x=> Order.smears C i.1 i.2 x t) (pairNames X (fun j=> atRef L _ r i (v j))).symm)

lemma limitHead {b:Filter UVIndex}[b.NeBot](he:b ≤ L.lens){v:UVIndex→ C.label D}{x:C.label D} (hx:Tendsto v b (𝓝 x))(h:C.ref D ≤ L.level r):
    Tendsto (fun i=>headMark L X D r i (v i)) b (𝓝 (X.charge F D (master L D r x))) :=by
   let m : Fin (X.n+1) → ℕ := Fin.cons (α:=fun _=>ℕ) D X.degree
   let Z (s:C.label D) : C.book.Vector m := Fin.cons (α:=fun i=> C.book.Ref (m i)) s (fun i=>S.representative _ (X.labels i))
   let t:= locatedRef L D r x
   let K(u):=atRef L D r u (v u)
   let P:= (fun x:C.book.Vector m=> fun i=>(⟨_,x i⟩:C.book.Token))
   have hs(w:C.label D): P (Z w)= Fin.cons (α:=fun _=> C.book.Token) ⟨D,w⟩ (refTags X) := by
       funext i; cases i using Fin.cases
       · simp only [Z,P, Fin.cons_zero]; rfl
       simp only [Z,P, Fin.cons_succ]; rfl
   have hk:= Next.UVStress.calibrated_smear (v:=fun i=> Z (K i)) (x:= Z t) F.room.ordered b (he.trans L.certified) X.test (he:=fun i=> by
       cases i using Fin.cases
       · simp only [Z,Fin.cons_zero]; exact tendsRef L he hx h
       simp only [Z,Fin.cons_succ]; exact tendsto_const_nhds)
   have hh:S.integralOn _ (Z t) X.test=X.charge F D (master L D r x):=by
       apply X.test.apply_eq; intro i hi; apply Eq.trans _ (X.pay_eq F D (master L D r x) i hi).symm
       have hp:= S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) hi (P (Z t)); refine hp.symm.trans (congr_arg _ ?_)
       rw [hs]; funext j; cases j using Fin.cases
       · simp only [Function.comp_apply,Fin.cons_zero]; exact congr_arg (fun v:S.Field D=> (⟨D,v⟩:S.Tag)) (payRef L x)
       simp only [Function.comp_apply,Fin.cons_succ]; change (⟨_,S.project _ (S.representative _ _)⟩:S.Tag)=_; rw [S.rep]; rfl
   rw [hh] at hk; exact hk.congr (fun i=> congr_arg (fun p=> Order.smears C i.1 i.2 p X.test) (hs (K i)))
end YM.RG17
namespace YM.RG17
open Function Set Filter MeasureTheory Extraction Table OPE OPE.Orbits RG12
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Spec.Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S)
    (L:Layout F) (loc:Located L) (X: External C S) {n:ℕ}
    {r:ℝ}{D:ℕ}{d e:Fin n→ℕ}

abbrev Comb {n:ℕ} (d:Fin n→ℕ):= (i:Fin n)→ Fin (d i+1)
abbrev Seats (C:Family G)(d:Fin n→ℕ):=(i:Fin n)→ (j:Fin (d i+1)) →ℝ→ C.label j
variable {v:(i:Fin n)→ Slot C (d i)} (p:Seats C d)
def branches (L:Layout F) (r:ℝ) (j:Comb d): Labels S (fun i=>j i) := fun i=> master L _ r (p i (j i) r)
def bank (L:Layout F)(p:Seats C d) (r:ℝ)(ψ:Test n)(X: External C S) (u:UVIndex):ℂ:= ∑ j:Comb d,
   packMark L X (fun i=>j i) (fun i=> p i (j i) r) r ψ u

def chair (P:Spec.Final C f S) (L:Layout P) (p:Seats C d)(i:Fin n) (j:Fin (d i+1)) (r:ℝ) := P.sector.derivatives.rise
       (Nat.le_of_lt_succ j.isLt) (master L _ r (p i j r))
def Weights (L:Layout F) (v:(i:Fin n)→ Slot C (d i))(p:Seats C d) : Prop :=
      ∀ᶠ r in home, ∀ i,stems L v r i= ∑ j, chair F L p i j r

-- existence of such weights with coarse λ price (not coupling-polynomial):
-- these are NOT necessarily the right pinned weights nor affordable at
-- diagram production cost.
include loc P
lemma someWeights (v:(i:Fin n)→ Slot C (d i)) : ∃ p:Seats C d,Weights L v p∧ ∀ i j,RateLE home OPE.run (p i j) 0 := by
   have hp (i:Fin n) (t:Slot C (d i)) : ∃ p: (j:Fin (d i+1))→ℝ→C.label j, (∀ j, RateLE home OPE.run (p j) 0)∧
      ∀ᶠ r in home,input L r (d i) t= ∑ j:Fin (d i+1), F.sector.derivatives.rise j.is_le (master L _ r (p j r)):=by
       rcases t with t|t
       · let V: C.label (Fin.last (d i)):=t
         let p(j:Fin (d i+1))(_:ℝ): C.label j:= (if h:j=Fin.last (d i) then h.symm ▸ V else 0)
         refine ⟨p,(fun j=> RateLE.const (p j 0) ageLarge),Eventually.of_forall fun r=> ?_⟩
         rw [Finset.sum_eq_single_of_mem (a:=Fin.last (d i)) (Finset.mem_univ _)]
         · change master L _ r t= _; simp only [p,dif_pos]; exact (F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts (master L _ r t)).symm
         intro b _ h; simp [p,h]
       exact loc.built (d i) t
   choose p h0 hp using (fun i=> hp i (v i))
   exact ⟨p,(eventually_all.mpr hp),h0⟩

omit loc

lemma seatedReadout (ψ:Test n) (hp: ∀ i,stems L v r i=∑ j,chair F L p i j r)(hr:r≠0)(hc:packs X r ψ):
  ∑ j : Comb d,(shape X r ψ).applyTo (fun y=> S.useAt S y (Fin.append (tags (branches p L r j)) X.tags)) =
       (shape X r ψ).applyTo (fun y=>S.useAt S y (Fin.append (tags (stems L v r)) X.tags)) :=by
   have hi(w:Labels S d) (x:Points n)(z:Points (X.n+1)): whole S (posed r x) w (X.offset z) X.labels =
       sectionLabels (d:=Sum.elim d X.degree) X.labels (m:= OPE.Orbits.moment S (beside (posed r x) (X.offset z))) w := (sectionLabels_apply ..).symm
   let t:= shape X r ψ
   let f (j:Comb d)(y):ℂ:= S.useAt S y (Fin.append (tags (branches p L r j)) X.tags)
   have hf:∀ j:Comb d, Integrable (fun y:Points (n+X.n)=> t y * f j y):=fun j=> t.smearing (show ContinuousOn (f j) (conf _) from (Next.UVStress.smoothDisc F.room.kernel.smooth _).continuousOn)
   change (∑ j:Comb d, ∫ y,t y* f j y)= ∫ y,t y *_
   rw [← integral_finsetSum _ (fun i _=> hf i)]; apply integral_congr_ae; filter_upwards with y; rw [← Finset.mul_sum]; by_cases hh:y∈tsupport t; swap
   · simp [image_eq_zero_of_notMem_tsupport hh]
   have hZ:= t.tsupport_subset hh; rw [show (⇑t)=_ from shaped X hr hc] at hh
   obtain ⟨⟨x,z⟩,-,rfl⟩:= absolute_lands X ψ.hasCompactSupport subset_rfl hr hh
   refine congr_arg (t _ * ·) ?_
   rw [← whole_absolutely (F:=F) X _ (x:=x) (z:=z) (r:=r) (by exact hZ),hi, funext hp]
   change _ = sectionLabels (d:=Sum.elim d X.degree) X.labels (m:= OPE.Orbits.moment S (beside (posed r x) (X.offset z))) (fun i=> ∑ j, chair F L p i j r)
   rw [MultilinearMap.map_sum]
   refine Finset.sum_congr rfl fun j _=> ?_
   have he:= (hi (fun i=>chair F L p i (j i) r) x z)
   apply Eq.trans _ he
   let Y:= beside (posed r x) (X.offset z)
   let g₀:= Sum.elim (fun i=> (j i).val) X.degree; let g:=Sum.elim d X.degree
   let u: Labels S g₀ := stages (branches p L r j) X.labels
   let w: Labels S g := stages (fun i=> chair F L p i (j i) r) X.labels
   have hv:g₀ ≤ g:=fun i=>by cases i with
                                  | inl i=> exact (j i).is_le
                                  | inr i=> exact le_rfl
   have hU (i):F.sector.derivatives.rise (hv i) (u i)=w i:=by
        cases i; · rfl
        exact F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts _
   refine ((whole_absolutely (F:=F) X (branches p L r j) (r:=r) (x:=x) (z:=z) (by exact hZ)).symm).trans ?_
   exact (OPE.Levy.inclusionMoment F g₀ _ hv u Y none ((rooted_packing ..).mpr hZ)).trans
      (congr_arg (Orbits.moment S Y) (funext hU))

include H loc
lemma limitBank (hv:Weights L v p) {K:Set (Points n)}(hk:IsCompact K)(hx:K⊆conf n):∀ᶠ r in home,
    ∀ ψ:Test n, tsupport ψ⊆K→ Tendsto (bank L p r ψ X) L.lens (𝓝 (appeared F (stems L v r) X r ψ)):=by
   have h₀: ∀ᶠ r in home, ∀ j:Comb d,∀ i:Fin n, C.ref (j i) ≤ L.level r := eventually_all.mpr fun j=>eventually_all.mpr fun i=>loc.level.growing.eventually_ge_atTop (C.ref (j i))
   filter_upwards [hv,h₀,positiveLength,roomFor X P H hk hx,appearedIntegrable (d:=d) P H hk hx X] with r hp hw hr hu he ψ hψ
   have hi := he (stems L v r) ψ hψ
   have hc:packs X r ψ:=fun x hx=>hu (image_mono (Set.prod_mono hψ subset_rfl) hx)
   rw [← chargedShape X (stems L v r) ψ hr hc hi,← seatedReadout P L X p ψ hp hr.ne' hc]
   letI := L.notbot; exact tendsto_finsetSum _ (fun i _=> limitPack L X le_rfl _ _ (hw i))
end YM.RG17

