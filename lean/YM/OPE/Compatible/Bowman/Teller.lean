import YM.OPE.Compatible.Bowman.Par
/-!
# No degree one. moment presorts paid.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{N:Side}{p q:Clip}{R T:PathData G}{P:Patch}{K:KernelChoices}{V:ChartRatio G}{i j t r n m d:ℕ}{s s' u b U e:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Planned.PrimaryIntegral295.Carrier
lemma glues_zero (h:G.Simple)(P:(r:ℕ)→Script (Shade G) r)(Y:∀ n:Side,Config G n→ℝ)(hp:Script.stint P 1 Y): P 1=0:=by
    have he: Idem (0:Script (Shade G) 1):=idemScale (P 1) 0 (hp.sym _)|>fun h=> by simpa using h
    apply away (folk_whole (hp.here 1)) summable_zero (hp.sym _) he epochX (tendsto_add_atTop_nat 1)
    refine Eventually.of_forall fun i v=> ?_; let n:=epochX i; obtain ⟨v,rfl⟩:=(spool G n).surjective v; let X:=Y n∘ represent; have hh:= hp.plot n; let f:= fderiv ℝ X 0
    have hf(k:G.El)(v:Bid.Dir G n): f (fun z=> G.adjoint k (v z))=f v:=by
       let K: Bid.Dir G n→L[ℝ] Bid.Dir G n:= (LinearMap.pi fun i=> G.adjoint k ∘ₗ LinearMap.proj (φ:=fun _ : Body 1 n=>G.Color) i).toContinuousLinearMap
       have he(v: Bid.Dir G n): represent (K v)= Lattice.gauge (fun _=>k) (represent v):=by funext i; erw [Work.F03.represent_link (K v) i]; rw [show K v _=G.adjoint k (v (i.1,coord i.2)) from rfl,adjoint_exp]; change _= _* represent _ _*_; rw [Work.F03.represent_link]
       exact chain_fixed K (Eventually.of_forall (fun v=> (show X (K v)= X v from by unfold X; simp only [Function.comp_apply,he,hp.stand]))) (hh.differentiableAt (by simp)) v -- param
    have hx:= slot_fixed h f hf v; have hK: narrate n (P 1) (spool G n v)=f v:=by
       change library n _ _ = _; rw [show (fun _ :Fin 1=>spool G n v)=(spool G n).toContinuousLinearMap ∘ (![v]:Fin 1→_) from funext fun i=>by fin_cases i;rfl,hp.wink n 1 le_rfl ![v],iteratedFDeriv_one_apply]; rfl
    rw [hK,hx]; simp [narrate,library,scribe]
variable (A:Alps B H i b) (L:Alps B H j U)
lemma soft_word (h:G.Simple): A.word 1=0:= glues_zero h _ _ (A.fullK _)
lemma soft_leaf (h:G.Simple): A.liftZ 1=0:= glues_zero h _ _ (A.fullL _)
lemma Poll_earn {I:Type*}(p:Script I (n+1))(c:ℝ)(h:p.Poll d):Poll (c • p) d:= by intro i l hi; change well (c • Script.crop p i) _=0; rw [wellScale, h _ _ hi,mul_zero]
lemma Poll_diff {I:Type}(p q:Script I (n+1))(h:p.Poll d)(he:q.Poll d)(hp:folk p)(hh:folk q):Poll (p-q) d:=by
    intro i l ht; let g:=tasting l; have hU:= flavor_part l d ht.le; rw [← show well (Script.crop p i) (tasting l)-well (Script.crop q i) (tasting l)=0 by rw [h i l ht,he i l ht,sub_self]]
    unfold well; rw [← (gardens hU (crops (hp d).choose_spec i)).tsum_sub (gardens hU (crops (hh d).choose_spec i))]; refine tsum_congr fun x=>?_; change (Script.crop p i x-Script.crop q i x)*_= _; ring
lemma pollzz (h:n ≤ 3): Poll (A.word (n+1)-L.word (n+1)) (4-n):=by
    unfold word inkV expose; rw [← smul_sub]; exact Poll_earn _ _ (mercy A.pays L.pays h)
lemma pollbb (h:n≤ 3): Poll (A.liftZ (n+1)) (4-n):=Poll_earn _ _ (mercyL A.pays h)
lemma comb_poll {P: Script (Shade G) (n+1)}(hp:Poll P d)(hk:folk P)(ht:P.pinned)(he:Flight i j)(hh:d≤ i)(h:0<s)(hQ:4 ≤ j): Poll (Script.mat G.ColorIndex he s P) d:=by
    intro j l hl; rw [globe_well P ((hk l.length).choose_spec) h hQ j l (fun x p h=>hp x p (h.trans hl)) le_rfl ht (hl.trans_le hh),hp _ _ hl,mul_zero]
end Alps
end YM.OPE.Votive
