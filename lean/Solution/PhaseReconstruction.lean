import YangMills.WilsonProof.PhaseAwards
import YM.Nonperturbative.HeadlineSpec
import YangMills.WilsonProof.Hierarchy
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YangMills.VacuumReconstruction

/-! Table laws and same-character Wightman reconstruction for a Wilson
limit. These lemmas apply to any final table, reader and completed phase atlas. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

noncomputable section
namespace IssuedExistencePhase.PhysicalTableLabels
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n : ℕ} {x : YM.Points n}

theorem filtration : Monotone (fun d => LinearMap.range ((hierarchy F Q).toLabel d)) := by
  rintro d e h _ ⟨v,rfl⟩
  exact ⟨_, F.sector.derivatives.stays F.room.kernel.laws.toSymmetric (spectate_ready F none) h v⟩

theorem unitInGrade (d : ℕ) :
    (hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour ∈ LinearMap.range ((hierarchy F Q).toLabel d) :=
  ⟨S.unit d, F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric (spectate_ready F none) F.room.kernel.laws⟩

theorem empty (s : Option (hierarchy F Q).Character) (v : Fin 0 → (hierarchy F Q).Tag)
    (x : YangMills.Points 0) : (hierarchy F Q).correlation s v x = 1 := by
  let w : Fin 0 → C.book.Token := Fin.elim0
  have h : S.classTokens ∘ w = v := funext (fun i => Fin.elim0 i)
  have hx : x ∈ conf 0 := fun k => Fin.elim0 k
  change S.useAt (spectator F s) x v = 1
  rw [← h,S.at_project (spectator F s) (spectate F s).laws.toSymmetric (spectate_respects F s) hx]
  exact (spectate F s).laws.trivial w x

theorem sameSlot (s : Viewers F) (hx : x ∈ conf n) (w : Fin n → S.Tag)
    (i : Fin n) (a b : S.Tag) (same : S.pin a.1 a.2 = S.pin b.1 b.2) :
    S.useAt (spectator F s) x (update w i a) = S.useAt (spectator F s) x (update w i b) := by
  rcases a with ⟨d,a⟩
  rcases b with ⟨e,b⟩
  let P := F.sector.derivatives
  have common : P.rise (le_max_left d e) a = P.rise (le_max_right d e) b := by
    apply S.pin_inj (max d e)
    rw [P.stays F.room.kernel.laws.toSymmetric (spectate_ready F none),
      P.stays F.room.kernel.laws.toSymmetric (spectate_ready F none)]
    exact same
  rw [← P.inclusion_slot (spectate_ready F s) (spectate F s).laws.toSymmetric (le_max_left d e) hx i w a,
    common, P.inclusion_slot (spectate_ready F s) (spectate F s).laws.toSymmetric (le_max_right d e) hx i w b]

theorem sameTuple (s : Viewers F) (hx : x ∈ conf n) (v w : Fin n → S.Tag)
    (same : ∀ i, S.pin (v i).1 (v i).2 = S.pin (w i).1 (w i).2) :
    S.useAt (spectator F s) x v = S.useAt (spectator F s) x w := by
  classical
  let A := fun (a : Finset (Fin n)) (i : Fin n) => if i ∈ a then v i else w i
  have applyAll (a : Finset (Fin n)) : S.useAt (spectator F s) x (A a) = S.useAt (spectator F s) x w := by
    induction a using Finset.induction_on with
    | empty => simp [A]
    | @insert i a hi ih =>
      have hprev : A a = update (A a) i (w i) := by
        funext k
        by_cases h : k = i
        · subst k
          simp [A,hi]
        · simp [update_of_ne h]
      have hnext : A (insert i a) = update (A a) i (v i) := by
        funext k
        by_cases h : k = i
        · subst k
          simp [A]
        · simp [A,h]
      rw [hnext, sameSlot F s hx (A a) i (v i) (w i) (same i), ← hprev]
      exact ih
  rw [← show A Finset.univ = v by simp [A]]
  exact applyAll _

end IssuedExistencePhase.PhysicalTableLabels
end

noncomputable section
namespace IssuedExistencePhase.PhysicalTableMultilinear
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
open IssuedExistencePhase.PhysicalTableLabels
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) {n : ℕ} (s : Viewers F) {x : YM.Points n}

def representative (a : S.Union) : S.Tag :=
  let witness := F.sector.derivatives.covered F.room.kernel.laws.toSymmetric (spectate_ready F none) a
  ⟨witness.choose,witness.choose_spec.choose⟩

theorem repPin (a : S.Union) : S.pin (representative F a).1 (representative F a).2 = a :=
  (F.sector.derivatives.covered F.room.kernel.laws.toSymmetric (spectate_ready F none) a).choose_spec.choose_spec

def value (x : YM.Points n) (v : Fin n → S.Union) :=
  S.useAt (spectator F s) x (representative F ∘ v)

theorem tagged (hx : x ∈ conf n) (v : Fin n → S.Tag) :
    value F s x (fun i => S.pin (v i).1 (v i).2) = S.useAt (spectator F s) x v :=
  sameTuple F s hx _ v (fun i => repPin F (S.pin (v i).1 (v i).2))

theorem fixedGrade (hx : x ∈ conf n) (d : ℕ) (v : Fin n → S.Field d) :
    value F s x (S.pin d ∘ v) = (S.classMoment (spectator F s) (fun _ => d) x) v :=
  tagged F s hx (fun i => ⟨d,v i⟩)

include F in
theorem commonGrade (v : Fin n → S.Union) (a b : S.Union) :
    ∃ (d : ℕ) (w : Fin n → S.Field d) (a' b' : S.Field d),
      v = S.pin d ∘ w ∧ a = S.pin d a' ∧ b = S.pin d b' := by
  let full : Fin (n+2) → S.Union := Fin.cons a (Fin.cons b v)
  obtain ⟨d,y,seen⟩ := F.sector.derivatives.joint F.room.kernel.laws.toSymmetric (spectate_ready F none) full
  refine ⟨d,fun i => y i.succ.succ,y 0,y (Fin.succ 0),?_,?_,?_⟩
  · funext i
    exact congrFun seen i.succ.succ
  · exact congrFun seen 0
  · exact congrFun seen (Fin.succ 0)

theorem updateGrade [DecidableEq (Fin n)] (d : ℕ) (w : Fin n → S.Field d) (i : Fin n) (y : S.Field d) :
    update (S.pin d ∘ w) i (S.pin d y) = S.pin d ∘ update w i y := by
  funext j
  by_cases eq : j = i
  · subst j
    simp
  · simp [eq]

noncomputable def moment (hx : x ∈ conf n) : MultilinearMap ℂ (fun _ : Fin n => S.Union) ℂ where
  toFun := value F s x
  map_update_add' v i a b := by
    obtain ⟨d,w,a',b',hv,ha,hb⟩ := commonGrade F v a b
    rw [hv,ha,hb,← map_add,updateGrade (S := S) d w i (a' + b'),updateGrade (S := S) d w i a',updateGrade (S := S) d w i b',
      fixedGrade F s hx,fixedGrade F s hx,fixedGrade F s hx]
    exact (S.classMoment (spectator F s) (fun _ => d) x).map_update_add w i a' b'
  map_update_smul' v i c a := by
    obtain ⟨d,w,a',_,hv,ha,_⟩ := commonGrade F v a a
    rw [hv,ha,← map_smul,updateGrade (S := S) d w i (c • a'),updateGrade (S := S) d w i a',fixedGrade F s hx,fixedGrade F s hx]
    exact (S.classMoment (spectator F s) (fun _ => d) x).map_update_smul w i c a'

theorem original (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Option (hierarchy F Q).Character) (n : ℕ) (x : YangMills.Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ measured : MultilinearMap ℂ (fun _ : Fin n => (hierarchy F Q).labels.carrier) ℂ,
      ∀ v : Fin n → (hierarchy F Q).Tag, (hierarchy F Q).correlation s v x =
        measured (fun i => (hierarchy F Q).toLabel (v i).1 (v i).2) := by
  refine ⟨moment F s hx, ?_⟩
  intro v
  exact (tagged F s hx v).symm

end IssuedExistencePhase.PhysicalTableMultilinear
end

noncomputable section
namespace IssuedExistencePhase.PhysicalTableUnit
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) {n : ℕ}

theorem first (s : Viewers F) (v : Fin n → S.Tag) {x : YM.Points (n+1)}
    (hx : x ∈ conf (n+1)) (d : ℕ) :
    S.useAt (spectator F s) x (Fin.cons ⟨d,S.unit d⟩ v) = S.useAt (spectator F s) (YM.Points.tail x) v := by
  let w : Fin n → C.book.Token := fun i => ⟨(v i).1,S.representative _ (v i).2⟩
  let raw : Fin (n+1) → C.book.Token := Fin.cons (C.book.one d) w
  have he (i) : S.classTokens (w i) = v i := by
    change Sigma.mk (v i).1 (S.project _ (S.representative _ _)) = v i
    rw [S.rep]
  rw [show (Fin.cons (α := fun _ => S.Tag) ⟨d,S.unit d⟩ v) = S.classTokens ∘ raw by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [raw,Function.comp_apply,Fin.cons_zero]
      rfl
    · simp only [raw,Function.comp_apply,Fin.cons_succ,he],
    S.at_project (spectator F s) (spectate F s).laws.toSymmetric (spectate_respects F s) hx,
    (spectate F s).laws.unital hx d w]
  rfl

theorem remove (s : Viewers F) (v : Fin (n+1) → S.Tag) (x : YM.Points (n+1))
    (hx : x ∈ conf (n+1)) (k : Fin (n+1)) (hk : S.pin (v k).1 (v k).2 = S.pin 4 (S.unit 4)) :
    S.useAt (spectator F s) x v =
      S.useAt (spectator F s) (WithLp.toLp 2 (x.ofLp ∘ k.succAbove)) (v ∘ k.succAbove) := by
  let p := (finSuccEquiv n).trans (finSuccEquiv' k).symm
  have p0 : p 0 = k := by simp [p]
  have pS (j : Fin n) : p j.succ = k.succAbove j := by simp [p]
  have unit : (v k).2 = S.unit (v k).1 := by
    apply S.pin_inj (v k).1
    exact hk.trans (F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric (spectate_ready F none) F.room.kernel.laws)
  have head : v k = (⟨(v k).1,S.unit (v k).1⟩ : S.Tag) := by
    rw [←unit]
  have inputs : v ∘ p = Fin.cons (α := fun _ => S.Tag) ⟨(v k).1,S.unit (v k).1⟩ (v ∘ k.succAbove) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Function.comp_apply,Fin.cons_zero,p0] using head
    · simp only [Function.comp_apply,Fin.cons_succ,pS]
  have points : YM.Points.tail (YM.Points.rearrange p x) = WithLp.toLp 2 (x.ofLp ∘ k.succAbove) := by
    apply WithLp.ofLp_injective
    funext j
    change x.ofLp (p j.succ) = x.ofLp (k.succAbove j)
    rw [pS]
  rw [← S.class_perm (spectator F s) (spectate F s).laws.toSymmetric p hx v,inputs,
    first F s _ (YM.Points.rearrange_in p hx), points]

theorem original (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Option (hierarchy F Q).Character) (v : Fin (n+1) → (hierarchy F Q).Tag)
    (x : YangMills.Points (n+1)) (hx : x ∈ WilsonFamily.separated (n+1)) (k : Fin (n+1))
    (hk : (hierarchy F Q).toLabel (v k).1 (v k).2 = (hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour) :
    (hierarchy F Q).correlation s v x =
    (hierarchy F Q).correlation s (v ∘ k.succAbove) (WithLp.toLp 2 (x.ofLp ∘ k.succAbove)) :=
  remove F s v x hx k hk

end IssuedExistencePhase.PhysicalTableUnit
end

noncomputable section
namespace IssuedExistencePhase.FieldTable
open YangMills
open Filter Function Set MeasureTheory
open scoped Topology
variable {g : GaugeGroup}

theorem tables {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
    (F : YM.Spec.Final C o S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) :
    Reconstruction.TableLaws (hierarchy F Q) where
  filtration := PhysicalTableLabels.filtration F Q
  unitInGrade := PhysicalTableLabels.unitInGrade F Q
  multilinear := PhysicalTableMultilinear.original F Q
  empty := PhysicalTableLabels.empty F Q
  unit s := fun {_} v => PhysicalTableUnit.original F Q s v
end IssuedExistencePhase.FieldTable
end

/- The contour-to-operator argument of YM.TraceExtension.Link.Identity, applied on
   the separately issued contour, real field system and field core of each elected character. -/
noncomputable section
namespace IssuedExistencePhase.OriginalPhaseUnits
open YM YM.TraceExtension
open Function Filter MeasureTheory YM.Boundary Set YM.Mink Complex YM.Table
open scoped Topology Classical InnerProductSpace ContDiff NNReal
variable {g : YangMills.GaugeGroup} {C : YM.Family g.core} {f : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : YM.Spec.Final C f S) (atlas : YM.EveryPhase.Almanac F) (chi : F.α.space.X) {d n : ℕ}
private def tearAt (i:Fin (n+1))(y: Points (n+1)) : Points n:= points fun j=>y (i.succAbove j)
private lemma east_tear (i:Fin (n+1))(x: Heights (n+1))(h:x∈east (n+1)): (x ∘ i.succAbove) ∈east n:=h.comp (Fin.strictMono_succAbove i)
private lemma strict_tear (i:Fin (n+1))(x: Times (n+1))(h:x∈strict (n+1)): (x ∘ i.succAbove) ∈strict n:=east_tear i (fun j=>(x j).im) h

private lemma use_unit {x : YM.Points (n+1)} (hx : x ∈ conf (n+1)) (i : Fin (n+1)) (v : Fin n → S.Tag) :
    S.useAt (F.α.ensemble chi) x (i.insertNth ⟨d,S.unit d⟩ v) = S.useAt (F.α.ensemble chi) (tearAt i x) v := by
  let w := i.insertNth (α := fun _ => S.Tag) ⟨d,S.unit d⟩ v
  have hw : S.pin (w i).1 (w i).2 = S.pin 4 (S.unit 4) := by
    have atI : w i = ⟨d,S.unit d⟩ := Fin.insertNth_apply_same i _ _
    exact (congrArg (fun a : S.Tag => S.pin a.1 a.2) atI).trans (F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric (YM.OPE.spectate_ready F none) F.room.kernel.laws)
  have del := IssuedExistencePhase.PhysicalTableUnit.remove F (some chi) w x hx i hw
  have eq : w ∘ i.succAbove = v := by funext j;exact Fin.insertNth_apply_succAbove ..
  rw [eq] at del
  exact del

private lemma waves_unit (i:Fin (n+1))(v:Fin n→S.Union)(x:SpacePoints (n+1)) (d:ℕ) :
    Set.EqOn (fun z : Times (n+1)=> (atlas.contours chi).waves.F _ z x (i.insertNth (S.pin d (S.unit d)) v))
      (fun z : Times (n+1)=> (atlas.contours chi).waves.F _ (z ∘ i.succAbove) (x ∘ i.succAbove) v) (strict (n+1)):=by
   let w:=(atlas.contours chi).waves
   have ht:= (atlas.cards chi).fromPhase
   let a':Times (n+1)→ₗ[ℂ] Times n:={toFun:=fun r=> r ∘ i.succAbove,map_add':=fun _ _=> rfl, map_smul':= fun _ _=> rfl}
   let b:=LinearMap.toContinuousLinearMap a'
   apply Next.BOUNDARY.ordered_eq _ _ (ht.heat.hol _ _ _) ((ht.heat.hol _ _ _).comp b.differentiable.differentiableOn (strict_tear i))
   intro t he
   obtain ⟨d',u,hu⟩:= F.sector.derivatives.joint F.room.kernel.laws.toSymmetric F.phase.transport.injection v
   let U(j):S.Tag:=⟨d',u j⟩
   have hz:v=fun j=> S.pin (U j).1 (U j).2:=hu
   let V:= i.insertNth (α:=fun _=>S.Tag) ⟨d,S.unit d⟩ U
   have hh:i.insertNth (α:=fun _=>S.Union) (S.pin d (S.unit d)) v= fun j => S.pin (V j).1 (V j).2:=by
       funext j
       induction j using Fin.succAboveCases i
       next => rw [Fin.insertNth_apply_same,show V i=⟨d,S.unit d⟩ from Fin.insertNth_apply_same ..]
       next j => rw [Fin.insertNth_apply_succAbove, show V (i.succAbove j)=U j from Fin.insertNth_apply_succAbove ..,hz]
   rw [hh,ht.heat.roots _ V _ t he,hz]
   change _=(atlas.contours chi).waves.F _ (fun j=> (↑((t ∘ i.succAbove) j):ℂ)*I) _ _
   rw[ht.heat.roots _ U _ _ (east_tear i t he)]
   unfold V; rw [use_unit F chi (clear he x)];rfl

private lemma slopes_unit (i:Fin (n+1))(d:ℕ)(v:Fin (n+1)→S.Union) (t:Fin (n+1)→Test4)(hv:v i=S.pin d (S.unit d))(p: Heights (n+1))(hp:p∈east (n+1))(s:ℝ)(hs:0<s):
    (atlas.contours chi).waves.atSlopes v p s (Joint.materialize _ t) = (∫ x:E4,t i x) * (atlas.contours chi).waves.atSlopes (v ∘ i.succAbove) (p ∘ i.succAbove) s (Joint.materialize n (t ∘ i.succAbove)):=by
    let k:= (fun _ : Fin (n+1)=> E4)
    let w:=(atlas.contours chi).waves; let q:=v∘i.succAbove; let X x:= w.restricted q (s • (p ∘ i.succAbove)) x* Joint.materialize n (t∘i.succAbove) x; let Z(y:E4 × (Fin n→E4)):= t i y.1 * X (points y.2)
    let A:= (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1)=> E4)).toHomeomorph.toMeasurableEquiv; let E := A.trans (MeasurableEquiv.piFinSuccAbove k i)
    have hE:MeasurePreserving E volume volume:= (volume_preserving_piFinSuccAbove k i).comp (Points.volume_product (n+1))
    have hV:v=i.insertNth (α:=fun _=>S.Union) (S.pin d (S.unit d)) q:= by funext j; induction j using Fin.succAboveCases i <;> simp [hv,q]
    have hH(x:Points (n+1)) : w.restricted v (s • p) x= w.restricted q (s • (p ∘ i.succAbove)) (tearAt i x):=by
        unfold Waves.restricted; rw [hV]; exact waves_unit F atlas chi i q (trace x) d (on_profile _ _ _ hs hp)
    unfold Waves.atSlopes
    calc
       _ = ∫ x:Points (n+1), Z (E x):=by
          apply integral_congr_ae; refine ae_of_all _ fun x=>?_
          change (atlas.contours chi).waves.restricted _ _ _ * _ = Z (E x)
          rw [show (atlas.contours chi).waves.restricted _ _ _=_ from hH x, Joint.material_at,i.prod_univ_succAbove _]; unfold Z X; rw [Joint.material_at]; change _ = t i (x i) * _; exact mul_left_comm _ _ _
       _ = ∫ y:E4 × (Fin n→ E4), Z y := hE.integral_comp E.measurableEmbedding Z
       _ = (∫ x:E4,t i x)*(∫ y: Fin n→ E4,X (points y)):=by unfold Z; exact integral_prod_mul (μ:=volume) (ν:=volume) (t i) (fun x=>X (points x))
       _ = _:=by
          congr 1; let B:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=> E4)).toHomeomorph.toMeasurableEquiv
          have ht:MeasurePreserving B volume volume:= Points.volume_product n
          exact ht.symm.integral_comp B.symm.measurableEmbedding X
lemma erase_unit (i:Fin (n+1))(d:ℕ)(v:Fin (n+1)→S.Union)(t:Fin (n+1)→Test4)(hv:v i=S.pin d (S.unit d)):
    (atlas.contours chi).world.W (n+1) v (Joint.materialize _ t)= (∫ x:E4,t i x)* (atlas.contours chi).world.W n (v ∘ i.succAbove) (Joint.materialize n (t ∘ i.succAbove)):=by
    let h:=(atlas.cards chi).fromPhase; let p: Heights (n+1):=fun i=>(i.val:ℝ)
    have he:p∈east _:=fun i j hi=> by simpa only [p,Nat.cast_lt] using (show i.val<j.val from hi)
    have hz:= h.emerges.profile _ v p he (Joint.materialize _ t)
    refine tendsto_nhds_unique hz ?_; exact ((h.emerges.profile _ (v∘i.succAbove) _ (east_tear i p he) (Joint.materialize n (t∘i.succAbove))).const_mul _).congr' ((show ∀ᶠ s:ℝ in 𝓝[>] 0,0 < s from self_mem_nhdsWithin).mono fun j hj=> (slopes_unit F atlas chi i d v t hv p he j hj).symm)

private lemma surf_get (W:Surface S)(v: Fin n → Letter S) :
    W.expect (List.ofFn v)= W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)):=by
   unfold Surface.expect
   let l:=List.ofFn v
   have hz : l.length=n:=List.length_ofFn
   have hP {A B:ℕ}(v: Fin A→ Letter S)(u: Fin B→Letter S)(h:A=B)(hu:∀ i, v i=u (Fin.cast h i)): W.W A (fun i=>(v i).1) (Joint.materialize A fun i=>(v i).2)= W.W B (fun i=> (u i).1) (Joint.materialize B fun i=>(u i).2):=by
       subst B; have ht:v=u:= funext hu;rw[ht]
   refine hP (fun i=> l.get i) v hz ?_
   intro i; simp[l,List.get_eq_getElem]; rfl

private lemma spell {X:Type*}(u v:List X)(p:X):∃ i:Fin ((u++v).length+1),
    let f:=i.insertNth (α:=fun _=>X) p (u++v).get
    List.ofFn f = u++ p::v:=by
   induction u with
   | nil=>
     change ∃ i:Fin (v.length+1),_
     refine ⟨0,?_⟩; intro f
     have hh:Fin.tail f=v.get:= funext fun j=> by rw [Fin.tail]; unfold f; simp
     rw [List.ofFn_succ]; change f 0 :: List.ofFn (Fin.tail f)= _; exact congr_arg₂ List.cons (by unfold f; simp;rfl) ((congr_arg List.ofFn hh).trans (List.ofFn_get v))
   | cons x u ih=>
     change ∃ i:Fin ((u++v).length+1+1),_
     obtain ⟨i,hI⟩:= ih
     let g:=i.insertNth (α:=fun _=>X) p (u++v).get
     refine ⟨i.succ,?_⟩; intro f
     have ht:f 0=x:=by change i.succ.insertNth (α:=fun _:Fin ((u++v).length+2)=>X) p (fun j => (x::(u++v)).get j) 0=x; rw [← show (i.succ).succAbove 0=(0:Fin ((u++v).length+2)) from Fin.succ_succAbove_zero _,Fin.insertNth_apply_succAbove]; rfl
     have hx: Fin.tail f=g:=by
        funext j; induction j using Fin.succAboveCases i
        next=> simp [Fin.tail,f,g]
        next j=> change i.succ.insertNth (α:=fun _:Fin ((u++v).length+2)=>X) p (fun j=> (x::(u++v)).get j) ((i.succAbove j).succ)= _; unfold g; rw[← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove,Fin.insertNth_apply_succAbove];rfl
     rw[List.ofFn_succ]; change f 0 :: List.ofFn (Fin.tail f)= _;rw[ht]; change x :: List.ofFn (show Fin ((u++v).length+1) → X from Fin.tail f)=x::(u++p::v); congr 1; exact (congr_arg List.ofFn hx).trans hI
lemma expect_unit (u v:Sentence S)(p: Test4) : (atlas.contours chi).world.expect (u++(S.pin d (S.unit d),p)::v)= (∫ x,p x) * (atlas.contours chi).world.expect (u++v):=by
    let W:=(atlas.contours chi).world; let g:= S.pin d (S.unit d); obtain ⟨i,hI⟩:= spell u v (g,p); let n:=(u++v).length; let y:Fin n → Letter S:=(u++v).get; let K:=i.insertNth (α:=fun _=>Letter S) (g,p) y
    have he:K i=(g,p):=Fin.insertNth_apply_same ..
    rw[← show List.ofFn K= _ from hI,surf_get,(congr_arg (atlas.contours chi).world.expect (List.ofFn_get (u++v))).symm]
    change _= (∫ x,p x)* W.expect (List.ofFn y)
    rw[surf_get]; let L:=Prod.fst ∘ K; let R:=Prod.snd ∘ K;
    have ht : K ∘ i.succAbove=y:= funext fun j=> Fin.insertNth_apply_succAbove ..
    have hh:= erase_unit F atlas chi i d L R (congr_arg Prod.fst he); simp_rw [show R i=p from congr_arg Prod.snd he,show L ∘ i.succAbove=Prod.fst ∘ y from ht ▸ rfl,show R ∘ i.succAbove=Prod.snd ∘ y from ht ▸ rfl] at hh; exact hh

open Fields
private lemma vectors_span (Y:Fields S)(hY:Y.Total) : Submodule.span ℂ (Set.range Y.evaluates) = ⊤:=by
   let P:=Submodule.span ℂ (Set.range Y.evaluates)
   have hx:(Set.range Y.vector)=Y.domain.subtype '' (Set.range Y.evaluates):= (range_comp _ _)
   apply (Submodule.map_injective_of_injective Y.domain.injective_subtype)
   have hp:=hY.cyclic; rw [hx,Submodule.span_image] at hp
   change P.map _= _; rw[← hp]; simp

lemma op_unit (v:Test4)(d:ℕ) :
    (atlas.actors chi).operators.field (S.pin d (S.unit d)) v= (∫ x,v x) • (LinearMap.id (R:=ℂ)):=by
   let W:=(atlas.actors chi).operators; let ψ:=(atlas.contours chi).world; let J:=(atlas.actors chi).J; let p:= (S.pin d (S.unit d),v); have H:= (atlas.cores chi); let c:=∫ x,v x
   let D:=W.domain
   have hx(i j:Sentence S): inner ℂ (W.evaluates i) (W.evaluates (p::j))=inner ℂ (W.evaluates i) (c • W.evaluates j):=by
      rw[inner_smul_right]; change inner ℂ (W.vector i) (W.vector (p::j))=c*inner ℂ (W.vector i) (W.vector j)
      rw [W.general _ H.meets _ H.adj,W.general _ H.meets _ H.adj]; exact expect_unit F atlas chi (Sentence.rev J i) j v
   have hspan : Submodule.span ℂ (range W.evaluates)=⊤:=vectors_span W H.total
   have hm(j:Sentence S): W.evaluates (p::j)=c • W.evaluates j:=by
       refine ext_inner_left ℂ fun x=>?_
       have he:x∈Submodule.span ℂ (range W.evaluates):=hspan ▸ Submodule.mem_top
       induction he using Submodule.span_induction with
       | mem w h=> rcases h with ⟨i,rfl⟩; exact hx i j
       | zero => simp
       | add x y _ _ h1 h2=>simp only[inner_add_left,h1,h2]
       | smul x y _ h=>simp only[inner_smul_left,h]
   ext1 i
   change W.field _ _ i= (c • LinearMap.id (R:=ℂ): D →ₗ[ℂ] D) i
   have he:i∈ Submodule.span ℂ (range W.evaluates):=hspan ▸ Submodule.mem_top
   induction he using Submodule.span_induction with
   | mem x h=> rcases h with ⟨j,rfl⟩; exact hm j
   | zero=> rw[map_zero,map_zero]
   | add x y _ _ hx hy=> rw[map_add,hx,hy,map_add]
   | smul a x _ hx=>rw[map_smul,hx,map_smul]
end IssuedExistencePhase.OriginalPhaseUnits
end

noncomputable section
namespace IssuedExistencePhase.OriginalPhaseContours
open YM YangMills Function Set Filter MeasureTheory
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary YM.EveryPhase
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (L : Almanac F) (valid : Completed F L) (i : F.α.space.X)

def actor : Σ H : HilbertSpace, WightmanTheory H (hierarchy F Q).labels :=
  ⟨stateSpace (L.actors i), view (L.actors i)⟩

theorem stress (a b : YM.Axis) :
    (actor F Q L i).2.adjointLabel (Reconstruction.minkowskiStress (hierarchy F Q) a b) =
      Reconstruction.minkowskiStress (hierarchy F Q) a b := by
  change (L.actors i).J (S.pin 4 (Stress.M F.sector.energy a b)) = S.pin 4 (Stress.M F.sector.energy a b)
  rw [(L.cores i).induced, Stress.M_Herm _ F.phase.transport.conserved F.phase.transport.spots F.phase.transport.spin]

theorem traced :
    (actor F Q L i).2.adjointLabel ((hierarchy F Q).toLabel 4 (hierarchy F Q).stressTrace) =
      (hierarchy F Q).toLabel 4 (hierarchy F Q).stressTrace := by
  change (L.actors i).J (S.pin 4 (TraceExtension.stressTrace F.sector.energy)) = S.pin 4 (TraceExtension.stressTrace F.sector.energy)
  rw [(L.cores i).induced]
  congr 1
  rw [Table.adj,LinearMap.comp_apply,show S.conj F.room.kernel.spin 4 (TraceExtension.stressTrace F.sector.energy) =
    TraceExtension.stressTrace F.sector.energy by simp only [TraceExtension.stressTrace,map_sum,F.phase.transport.conserved.real],
    ← F.phase.transport.spots.signed,TraceExtension.stressTrace_turn F.phase.transport.spin]

theorem centered :
    (actor F Q L i).2.adjointLabel ((hierarchy F Q).toLabel 4 (hierarchy F Q).centeredTrace) =
      (hierarchy F Q).toLabel 4 (hierarchy F Q).centeredTrace := by
  change (L.actors i).J (S.pin 4 (TraceExtension.theta (spectator F (some F.α.atPoint)) F.sector.energy)) = S.pin 4 (TraceExtension.theta (spectator F (some F.α.atPoint)) F.sector.energy)
  rw [(L.cores i).induced, TraceExtension.trace_adj F.phase.transport.conserved F.phase.transport.spin F.phase.transport.spots
    (spectate_respects F (some F.α.atPoint)) (spectate F (some F.α.atPoint))]

theorem shiftEq {n : ℕ} (r : ℝ) (height : Fin n → ℝ) (x : YangMills.Points n) :
    Hierarchy.complexShift r height x = YM.Boundary.shift x (r • height) := by
  funext j
  simp [Hierarchy.complexShift,YM.Boundary.shift,Pi.smul_apply,YangMills.time,YM.time]

theorem spaceEq {n : ℕ} (x : YangMills.Points n) : Hierarchy.spatialPoints x = YM.Boundary.trace x := rfl

def source (identity : ∀ t : TestFunction,
    (actor F Q L i).2.fields.field ((hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour) t =
    (∫ x,t x) • LinearMap.id (R := ℂ)) :
    Reconstruction.PhaseSource (hierarchy F Q) i (actor F Q L i).1 (actor F Q L i).2 where
  axioms := view_axioms _ (valid.isTheory i)
  faithful := (L.cores i).faithful
  translations _ v := (L.cores i).letters.identity v
  commonAdjoint := L.letters i
  unitOperator := identity
  stressAdjoint := stress F Q L i
  traceAdjoint := traced F Q L i
  centeredAdjoint := centered F Q L i
  wave := (L.contours i).waves.F
  surface := (L.contours i).world.W
  continuous := (L.cards i).fromPhase.heat.together
  holomorphic := (L.cards i).fromPhase.heat.hol
  euclidean n v x hx := by
    have h := (L.cards i).fromPhase.heat.roots n v (Hierarchy.spatialPoints x) (fun j => YangMills.time (x j)) hx
    have e : YM.Boundary.place (Hierarchy.spatialPoints x) (fun j => YangMills.time (x j)) = x := by
      apply PiLp.ext
      intro j
      exact YM.position_eta (x j)
    rw [e] at h
    exact h
  sliceGrowth n v := by
    obtain ⟨Y,ident,_⟩ := (L.cards i).reveals
    have paid := Y.power.1 n v
    rw [ident] at paid
    obtain ⟨m,K,ge,all⟩ := paid
    refine ⟨m,K,ge,?_⟩
    intro height gap pos separated x
    rw [shiftEq,one_smul]
    exact all height gap pos separated x
  integrable n v height order r pos t := by
    have h : (r • height) ∈ YM.Boundary.east n := fun _ _ hit => mul_lt_mul_of_pos_left (order hit) pos
    have actual := (L.cards i).fromPhase.emerges.int n v _ h t
    simp only [shiftEq,spaceEq,YM.Boundary.Waves.restricted] at actual ⊢
    exact actual
  boundary n v height order t := by
    have actual := (L.cards i).fromPhase.emerges.profile n v height order t
    simp only [shiftEq,spaceEq,YM.Boundary.Waves.atSlopes,YM.Boundary.Waves.restricted] at actual ⊢
    exact actual
  tensor n v tests := ⟨YM.Boundary.Joint.materialize n tests,
    fun x => YM.Boundary.Joint.material_at tests x, (publicMoment _ (L.cores i).meets n v tests).symm⟩

end IssuedExistencePhase.OriginalPhaseContours
end

noncomputable section
namespace IssuedExistencePhase.VacuumReconstruction
open YangMills
open Filter Function Set MeasureTheory
open scoped Topology
variable {g : GaugeGroup}

def phases {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
    (F : YM.Spec.Final C o S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (L : YM.EveryPhase.Almanac F) (valid : YM.EveryPhase.Completed F L) :
    Reconstruction.Phases (hierarchy F Q) where
  phaseTheory := OriginalPhaseContours.actor F Q L
  continuedStress := WilsonProof.PhaseAwards.continuedStress Q L
  source i := OriginalPhaseContours.source F Q L valid i (fun t => OriginalPhaseUnits.op_unit F L i t 4)
  selectedTheory := congrArg (fun a : YM.Boundary.Wightman S =>
    (⟨stateSpace a,view a⟩ : Σ H : HilbertSpace, WightmanTheory H (hierarchy F Q).labels)) L.baseR
  selectedTube n v z _ space := by
    change (L.contours F.α.atPoint).waves.F n z space (fun j => S.pin (v j).1 (v j).2) =
      F.A.waves.F n z space (fun j => S.pin (v j).1 (v j).2)
    rw [L.baseB]
  characterContinuity := valid.depends
end IssuedExistencePhase.VacuumReconstruction
end
