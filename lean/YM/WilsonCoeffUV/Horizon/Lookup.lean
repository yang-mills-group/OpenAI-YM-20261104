import YM.WilsonCoeffUV.Root.UV.HorizonD
/-!
# Filtered restriction of the endpoints

This controls engineering caps at the terminals *before a change of calibration*.
Beware: normalizing S on its own h, changing h and reinverting the larger
matrix and then just dropping letters is NOT this relation.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a t N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}

-- Engineering only. Full read on arbitrary p:(Jet G), not restricted hol neighborhood.
def studS (G:Gauge){k h:ℕ} (_t : h≤ k) : Snap G h →ₗ[ℝ] Snap G k where
    toFun p:= trunk k (expand h p)
    map_add' P Q :=by funext i; unfold trunk expand; rw [Pi.add_apply]; split <;> simp
    map_smul' r X:=by funext i; unfold trunk expand; rw [Pi.smul_apply]; split <;> simp
lemma curtain (t:h≤k)(p:Snap G h): expand k (studS G t p)=expand h p:=by
    funext i; change expand k (trunk k (expand h p)) i=_; unfold expand; split
    next=> rfl
    next h'=> rw [dif_neg (by omega)]
lemma entire (t:h≤k)(w:Snap G h): potential k (expand h w)= potential h (expand h w):=by
    funext i x; unfold Source.potential; symm
    apply Finset.sum_subset (Finset.range_mono (by omega)); intro j u hu
    rw [expand, dif_neg (by simpa only [Finset.mem_range] using hu)]; rfl
lemma accord (H:Hol G)(t:h≤k)(w:Snap G h): pureQuest H (studS G t w)=pureQuest H w:=by
    funext l; apply congr_fun (_ : H.flow k _ 1 l= H.flow h _ 1 l)
    have he : partConnection k (expand k (studS G t w)) 1 l=partConnection h (expand h w) 1 l:=by funext i; rw [partConnection,curtain t,entire t]; rfl
    exact (H.solves k _ 1 l).unique (he.symm ▸ H.solves h _ 1 l)
lemma lowLanes (H:Hol G)(t:h≤k)(x:YForest G)(X:Snap G h):flex (h:=k) x (studS G t X)=flex x X:=by
    let v:= feather x; change (Film.lane (Place.seat (feather x).1) (feather x).2 _) x.2.2=(Film.lane (Place.seat (feather x).1) (feather x).2 X) x.2.2; rw [Film.lane_truth H (feather x),Film.lane_truth H (feather x),accord H t X]
lemma shelves (H:Hol G)(t:h≤k)(x:Fin r→YForest G)(l:ℕ)(X:Snap G h): Tensor.diagonal (latent (skyline k x l)) (studS G t X)= Tensor.diagonal (latent (skyline h x l)) X:= by
   rw [lost,lost]; apply congr_arg (leading l); funext q
   rw [←map_smul]; unfold mite; simp_rw [lowLanes H t]
lemma engines (t:h≤k)(Y:Snap G h)(v:ℝ): engineered v (trunk k (expand h Y))= studS G t (engineered v Y):=by
    funext j; change v^(_ : ℕ) • expand h Y j.val=expand h _ j.val; unfold expand; split
    · rfl
    exact smul_zero ..
lemma tracesS (H:Hol G)(t:h≤k)(c: Embroider.Volume D)(F:ChamberTen G (Vote D) r){s A:ℝ}(v:Twig 0 s A F)(p:0<s)(d:mural F)(n l:ℕ)(y:n≤h):
    seedTile (arret c F k l) n = seedTile (arret c F h l) n:=by
    let f:=arret c F k l; let g:=arret c F h l; let a:=seedTile f n; let b:=seedTile g n
    have hb(Y:Snap G h): vein f (expand h Y)=vein g (expand h Y):=by
       funext q; unfold vein; rw [engines t,trunks,lat_sum c F k l v p,lat_sum c F h l v p]; refine tsum_congr fun i=>?_; rw [shelves H t]
    have hB : a ∈ limited G h:=by
        apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr; intro i u
        have he:=seed_grade f n (MvPolynomial.mem_support_iff.mp u); rw [weight_slot] at he; exact (show height i=n from congr_arg Prod.fst he).trans_le y
    have hR : a∈ localFields G h:= ⟨hB,(seed_paint H c v p d k l (y.trans t)).2⟩
    have hA : b∈ localFields G h:= seed_paint H c v p d h l y
    apply eval_ext; intro J
    change read J a= read J b; rw [← show read (expand h (trunk h J)) a = _ from racts ⟨a,hR⟩ J,← show read (expand h (trunk h J)) b = _ from racts ⟨b,hA⟩ J,show a=seedTile f n from rfl,show b=seedTile g n from rfl,reads_seedTile,reads_seedTile,hb]

-- any graded physical restriction respecting supplied labels. pay with Card here only.
structure LabelsHold (F:Frame G h)(Y:Frame G k)(t:h≤ k) where
    moon : F.Index ↪ Y.Index
    faith i: Y.basis (moon i)=raiseLabel G t (F.basis i)

lemma LabelsHold.earn {Y:Frame G k}{t:h≤k}(K:LabelsHold F Y t)(i:F.Index): Y.grades (K.moon i)=F.grades i:=by
    have he: Y.basis (K.moon i) ∈ Grade (F.grades i):=K.faith i ▸ F.pure i
    apply pure_unique (Y.basis.ne_zero _) _ _ (Y.pure _) he
lemma LabelsHold.picture {Y:Frame G k}{t:h≤k}(K:LabelsHold F Y t)(i:Alma F):
    let s:=notar F i; (weight F i)=(Y.grades (K.moon (sheet F i))).1+s.val.card:=by intro s; unfold weight weave; rw [K.earn]; rfl

def climbC {Y:Frame G k}{t:h≤k}(K:LabelsHold F Y t)(i:Alma F): Alma Y := by
    refine ⟨(K.moon (sheet F i),⟨(notar F i).val,(notar F i).property.trans t⟩),?_⟩
    change (Y.grades _).1 + (notar F i).val.card ≤ _; exact le_trans (K.picture i).symm.le ((weigh_cap F i).trans t)
lemma climb_inj {Y:Frame G k}{t:h≤k}(K:LabelsHold F Y t): Injective (climbC K):=by
    intro i j h; have he:sheet F i=sheet F j:=K.moon.injective (congr_arg (sheet Y) h); have ht:notar F i=notar F j:=Subtype.ext (congr_arg (fun i:Alma Y=>(notar Y i).val) h); exact Subtype.ext (Prod.ext he ht)
lemma career {Y:Frame G k}{t:h≤k}(K:LabelsHold F Y t)(i: F.Index)(v:Label G h): Y.coords (raiseLabel G t v) (K.moon i)=F.coords v i:=by
    have he (u:F.Index) (a:ℂ): Y.coords (raiseLabel G t (a • F.basis u)) (K.moon i)= F.coords (a • F.basis u) i:=by rw [map_smul,←K.faith u,map_smul,map_smul,F.coords_basis,Y.coords_basis]; by_cases H:i=u <;> simp [*]
    rw [← F.basis.sum_repr v]; simp only [map_sum,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> he _ _
lemma wreathLoans {Y:Frame G k}{t:h≤k} (K:LabelsHold F Y t)(i: Alma F)(H:Hol G)(u:ChamberTen G (Vote D) r){s A:ℝ}(p:Twig 0 s A u)(b:0<s)(d:mural u): trellis Y u (climbC K i)=trellis F u i:=by
    let Q:=K.moon; let X:= climbC K i; let l:=valence F i; let c:=brow F i D; let a:= weave F i
    have hm: a≤h:= F.bound _
    have ht : F.grades (sheet F i)= Y.grades (sheet Y X):=(K.earn (sheet F i)).symm
    have he : valence F i=valence Y X:=congr_arg Prod.snd ht; have hz: weave F i=weave Y X:=congr_arg Prod.fst ht
    rw [trellis,show weave Y (climbC K i)=a from hz.symm,show valence Y (climbC K i)=l from he.symm,show brow Y (climbC K i) D=c from rfl,detecting _ _ _ (seed_paint H c p b d k l (hm.trans t)),trellis];
    let v: Label G h:=⟨seedTile (arret c u h l) a,seed_paint H c p b d h l hm⟩; have hV: (⟨_,seed_paint H c p b d k l (hm.trans t)⟩:Label G k)=raiseLabel G t v:=Subtype.ext (tracesS H t c _ p b d a l hm)
    rw [hV]; rw [show sheet Y (climbC K i)= K.moon _ from rfl,career K,detecting _ _ _ (seed_paint H c p b d h l hm)]
lemma bridal {Y:Frame G k}{t:h≤k} (K:LabelsHold F Y t) (W:Single G D)(m:ℕ)(i:Alma F)(H:Hol G)(v:∀ j r, j ≤ m → r ≤ valence F i→ mural (W j r) ∧∃ s A,0<s∧Twig 0 s A (W j r)):
    glean Y W m (climbC K i)=glean F W m i:=by
    have ht:valence Y (climbC K i)=valence F i:=congr_arg Prod.snd (K.earn _)
    unfold glean; dsimp only; rw [ht]; apply Finset.sum_congr rfl; intro j hj; split; rename_i h'
    · obtain ⟨p,s,a,x,y⟩:= v (m+j-valence F i) j (by have hv:=Finset.mem_range.mp hj; omega) (by have hv:=Finset.mem_range.mp hj; omega); unfold echoS; rw [wreathLoans K i H _ y x p]
    rfl
lemma linked_book (F:Labels.Frames G)(i:ℕ): Nonempty (LabelsHold (F.level i) (F.level (i+1)) (by omega)):=by
    let L:=F.level i; let V:= F.level (i+1)
    choose f he using fun j=> F.coherent i (show raiseLabel G _ (L.basis j)∈ Set.range ((raiseLabel G _) ∘ (F.level i).basis) from ⟨j,rfl⟩)
    refine ⟨⟨⟨f,?_⟩,he⟩⟩
    intro a b h; apply L.basis.injective; have hX:raiseLabel G i.le_succ (L.basis a)= raiseLabel G i.le_succ (L.basis b):= by rw [← he a,← he b,h]
    exact Submodule.inclusion_injective _ hX
lemma brady (F: Labels.Frames G)(h:t≤q):Nonempty (LabelsHold (F.level t) (F.level q) h) := by
    induction q,h using Nat.le_induction with
    | base=> exact ⟨⟨Function.Embedding.refl _,fun _=> rfl⟩⟩
    | succ k h ih=> obtain ⟨I⟩:= ih; obtain ⟨X⟩:=linked_book F k
                    refine ⟨⟨I.moon.trans X.moon,fun j=>?_⟩⟩; rw [Function.Embedding.trans_apply,X.faith,I.faith]; rfl
end YM.WilsonCoeffUV.Cosmos
