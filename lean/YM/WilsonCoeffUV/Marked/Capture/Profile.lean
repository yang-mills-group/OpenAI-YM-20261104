import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.WilsonCoeffUV.Product.Report.ReportStability
/-!
# Profile consumption (root alignment in model)

Use EXACT gears and projections from normalized top. No discrepancy from model
reserve cropping, for profiles with head separation. Full product in Era equals
the one used in Mer. Unmasked before physical approximation. Every mark in
master, before `read`. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{o:ι}{c:Side}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C x y z ρ:ℝ}{E W V' U':Credit}
variable [DecidableEq ι][Fintype ι]

abbrev Garland (D:ι→ℕ):= ∀ i,Rarity (D i)
def lyra (u y:ℝ)(z:CellR)(F:Garland D)(x:ι→Cover)(i:ι):Volume (D i):= wheelC u y (x i) (F i).ψ z
def scrollR (u y:ℝ)(z:CellR)(F:Garland D)(X:Outerm G D)(x:ι→Cover): Era G ℝ:= tuftV (touch (lyra u y z F x) Finset.univ) (X x Finset.univ)
def boxes (x y:ℝ)(F: Garland D): Finset (ι→Cover):= Fintype.piFinset (fun i=>canvasM (F i) x y)
omit [DecidableEq ι] [Fintype ι] in
lemma testW (A:Case D)(p:o∈S)(u:A o=0)(Z:Era G (Pen D S)): tuftV (touch A S) Z=0:=by
    have ht: seaMark A S=0:= Subtype.ext (ContinuousMap.ext fun x=> by change folio _ _ _=0; unfold folio; change (∏ i∈S,_)=0; apply Finset.prod_eq_zero p; rw [u]; rfl)
    rw [touch,ht,map_zero]; unfold tuftV; ext1; · funext n i j x; rfl
    funext i j x; rfl
lemma scrollR_null (T:Outerm G D)(z:CellR)(F:Garland D)(s:ι→Cover)(u:0<x)(p:s ∉ boxes x y F): scrollR x y z F T s=0:=by
    simp only [boxes,Fintype.mem_piFinset,not_forall] at p
    obtain ⟨i,h⟩:=p; exact testW (lyra x y z F s) (Finset.mem_univ i) (not_ne_iff.mp fun p=> h (contour _ x y z _ u p)) _

def allσ : Finset ι:= Finset.univ
abbrev fullK (k:ι→ℕ) := mass k Finset.univ
def lyric (v:ℝ)(k:ι→ℕ) := ∏ i, drumB (k i) v
def Finale (u y:ℝ)(z:CellR)(F:Garland D)(k:ι→ℕ)(X:Outerm G D) : Era G ℝ := ∑ p ∈ boxes u y F, lyric u k • scrollR u y z F X p
lemma Finale_Auth (u y:ℝ)(z:CellR)(F:Garland D)(L:ι→ℕ)(X:Outerm G D)(p:Solo k X): Auth (fullK k) (Finale u y z F L X):= Auth.sum fun x _=> ((p x Finset.univ).tuft _).μ _
lemma hop0 {O:CellR}(P:Patch)(F:Garland D)(v:ι→Cover)(w:backRow P.L Finset.univ)(x y:ℝ): lyra x y O F (splitQ P v Finset.univ w) = laid P (inflate P Finset.univ w) (lyra (x*P.L.val) y O F v):=funext fun i=>eyelet P x y (v i) _ _ O
lemma stone_pull (P: Patch) (F:Garland D)(v:ι→Cover)(w:backRow P.L Finset.univ)(x y:ℝ)(O:CellR)(X: Era G (Pen D Finset.univ)):
    tuftV (touch (lyra x y O F (splitQ P v Finset.univ w)) _) X=tuftV (touch (lyra (x*P.L.val) y O F v) _) (tuftV (mend P (inflate P Finset.univ w) D Finset.univ) X):= by
    rw [hop0]; apply Prod.ext <;> first | exact funext (fun n=>funext fun i=>funext fun j=>funext fun x=> Eq.symm (mend_v ..)) | exact funext (fun i=>funext fun j=>funext fun x=>Eq.symm (mend_v ..))
omit [DecidableEq ι] in
lemma scale_prod (P:Patch)(x:ℝ)(h:0<x)(k:ι→ℕ): lyric x k=lyric (x*P.L.val) k*scalesK P k Finset.univ:=by
    unfold lyric scalesK; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; unfold drumB; field_simp; ring
lemma scroll_one (P:Patch)(w:Garland D)(u y:ℝ)(z:CellR)(p:ι→Cover)(X:Outerm G D)(v:backRow P.L Finset.univ)(e:0<u):
    lyric u k • scrollR u y z w X (splitQ P p Finset.univ v)= lyric (u*P.L.val) k • tuftV (touch (lyra (u*P.L.val) y z w p) _) (portV P k X p Finset.univ v):=by
    let A:= splitQ P p Finset.univ v; unfold scrollR; rw [stone_pull,scale_prod P u e k,mul_smul];
    unfold portV; congr 1
lemma gauge_reveal (P:Patch)(X:Outerm G D)(F: Garland D)(u y:ℝ)(z:CellR)(q:0<u)(k:ι→ℕ): Finale u y z F k X= Finale (u*P.L.val) y z F k (unite P k X):=by
    let e (p: (ι→ Cover) × backRow P.L Finset.univ):= splitQ P p.1 Finset.univ p.2; let C:= boxes u y F; let v:=u*P.L.val; let T:=boxes v y F; let f (p:ι→Cover):= lyric u k • scrollR u y z F X p
    have hu: Injective e:=by
       intro a b h; have hx i: inflate P Finset.univ a.2 i= inflate P Finset.univ b.2 i ∧ a.1 i=b.1 i:= (by
           have he:(a.1 i,inflate P Finset.univ a.2 i)=(b.1 i,inflate P Finset.univ b.2 i):= heapZ_inj P (congr_fun h i); exact ⟨congr_arg Prod.snd he, congr_arg Prod.fst he⟩)
       refine Prod.ext (funext fun i=> (hx i).2) (funext fun p=>?_); have ht:inflate P Finset.univ a.2 p.val=a.2 p:=dif_pos p.property; rw [←ht,(hx p.val).1]; exact dif_pos p.property
    let Q := T.product (Finset.univ:Finset (backRow P.L (Finset.univ:Finset ι))); let W:= Q.image e
    have hx: ∑ p∈ C,f p=∑ p∈W,f p:=by
       let J:=W∪C
       refine (Finset.sum_subset Finset.subset_union_right ?_ : (∑ i∈C,f i)= ∑ i∈ J,f i).trans (Finset.sum_subset Finset.subset_union_left ?_ : (∑ i∈W,f i)= ∑ i∈J,f i).symm
       · intro i _ p; unfold f; rw [scrollR_null _ _ _ _ q p, smul_zero]
       intro i _ h
       let A j:= parentC P.L (i j); let Y (p:↥(Finset.univ:Finset ι)):= wrap P.L (i p.val); have he:e (A,Y)=i:= by funext a; unfold e splitQ copyQ; rw [inflate,dif_pos (Finset.mem_univ _)]; exact heapZ_eq P _
       unfold f; rw [←he,scroll_one P _ u y z _ X _ q]
       have hz:A∉T:= fun p=> h (Finset.mem_image.mpr ⟨(A,Y),Finset.mem_product.mpr ⟨p,Finset.mem_univ _⟩,he⟩)
       simp only [T,boxes,Fintype.mem_piFinset,not_forall] at hz; obtain ⟨s,hp⟩:= hz
       have hT : lyra v y z F A s=0:= not_ne_iff.mp (fun h=> hp (contour _ v _ z _ (by unfold v; positivity) h)); rw [testW (lyra v y z F A) (Finset.mem_univ s) hT,smul_zero]
    unfold Finale; rw [hx]; unfold W; rw [Finset.sum_image (fun x _ y _ p=>hu p)]; unfold Q; rw [show (T.product _) = T ×ˢ Finset.univ from rfl,Finset.sum_product]
    refine Finset.sum_congr rfl fun i _=>?_; unfold f; simp_rw [show ∀ j,scrollR u y z F X (e (i,j)) = scrollR u y z F X (splitQ P i Finset.univ j) from fun _=>rfl, scroll_one P F u y z i X _ q, ← Finset.smul_sum]; apply congr_arg (lyric v k • ·)
    apply Prod.ext; · funext n; simp only [scrollR,tuftV, Prod.fst_sum, unite,Finset.sum_apply,map_sum]
    simp only [scrollR, tuftV, Prod.snd_sum, unite,map_sum]
end YM.WilsonCoeffUV.Wheel.Flooring
