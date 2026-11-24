import YM.WilsonCoeffUV.Root.UV.Names
/-!
# Changing jet/test horizon *D*. Cups compatible on profiles. Ancilla h still the own-horizon! -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}
-- identity of value and continuous maps. D→D' restrict profiles.
def scrollD (u:D≤ l):Scroll l→ₗ[ℝ] Scroll D where
    toFun f:=⟨f.val,scribble f u⟩
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
lemma pagesD (u:D≤ l): ∃ D':Volume l→L[ℝ]Volume D,(∀ f:Scroll l,D' (page l f)= page _ (scrollD u f)) ∧ ‖D'‖≤ 1:=by
    refine factoring (page l) (LinearMap.comp (page D) (scrollD u)) (submitted (D:=l)) 1 zero_le_one (fun f=>?_)
    rw [one_mul]; apply pledge (scrollD u f) (norm_nonneg _); exact fun i h w v=>creased f (h.trans u) w v
def portalV (u:D≤l):Volume l→L[ℝ]Volume D := (pagesD u).choose
lemma portage (u:D≤l)(x:Scroll l): portalV u (page _ x)=page _ (scrollD u x):=(pagesD u).choose_spec.1 x
def voteD (u:D≤l): Vote D →L[ℝ] Vote l:= ContinuousLinearMap.precomp ℝ (portalV u)
lemma jewelC (i:Alma F)(p:h<D)(u:D≤l)(v:h<l): jewelBloom v i= voteD u (jewelBloom p i):=by ext1 x; obtain ⟨t,rfl⟩:= submitted x; change _=jewelBloom p i (portalV u (page l t)); rw [portage]; rfl
lemma porch (u:D≤l)(P:Patch)(i:Site P.L)(v:Volume l): portalV u (foldWord P i l v)= foldWord P i D (portalV u v):=by obtain ⟨f,rfl⟩:=submitted v; rw [observed,portage,portage,observed]; rfl
-- P,VaryT and rail

abbrev leanTex (u:D≤l)(P:Pal (Vote D) U): Pal (Vote l) U:=fun i=> cloaks (voteD u).toLinearMap (P i)
def leanPanel (u:D≤l)(P:Island F D): Island F l:= (fun n i=> leanTex u (P.1 n i), fun i=> leanTex u (P.2 i))
lemma encoreT (P:Patch)(w: Site P.L){W:Type}[AddGroup W](p:W)(u:D≤l)(Y: Pal (Vote D) (W×U)): gatherT P w p (leanTex u Y)=leanTex u (gatherT P w p Y):=by
   ext i r x v; change Y i r _ (portalV u (foldWord P w l v))=_; rw [porch]; rfl
lemma fixGrade (C:Cost)(u:D≤l)(Y:Pal (Vote D) U): Blue.mix C (leanTex u Y)= leanTex u (Blue.mix C Y):=by
   funext i j
   funext v
   change Blue.mix C (leanTex u Y) i j v=voteD u (Blue.mix C Y i j v); simp only [Blue.mix, Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]; rfl
lemma apprise (A:Levels G)(Ñ:ChartRatio G)(u:D≤l)(Y: Vell G (n*(ll A m).L) D)(N h:ℕ): cloakP A Ñ N m h n (leanTex u Y)=leanTex u (cloakP A Ñ N m h n Y):=by
    let P:= ll A m; let L:=roam A N m; let K:= A.clock.kernel; let H:= freeForms A N (m+1); let W:= (story A Ñ N (m+1)).1 (n*P.L)
    let t:_:=bellOne P K Ñ H L h D (n:=n)
    have he w: bellOne P K Ñ H L h l w (n:=n) W (leanTex u Y)=leanTex u (t w W Y):=by unfold bellOne; rw [encoreT]; exact (reed_maps _ _ _ _ _ (voteD u).toLinearMap (w:=gatherT P w _ Y)).symm
    have hv: collarT P K Ñ H L h l (n:=n) W (leanTex u Y)=leanTex u (collarT P K Ñ H L h D (n:=n) W Y):=by
       simp_rw [collarT, he]; funext i; simp only [Pi.smul_apply,Finset.sum_apply,leanTex,map_smul,map_sum]; rfl
    unfold cloakP; rw [hv]; exact fixGrade ..
lemma angleD (u:D≤l)(A:Coil F)(P:BookC F (Vote D) U)(i): impose (fun i=> leanTex u (P i)) A i=leanTex u (impose P A i):= by funext i; simp only [impose,leanTex,affix, Finset.sum_apply,map_sum,map_smul]
lemma imprintD (u:D≤l)(P:Island F D)(T:Coil F): imprint (leanPanel u P) T= leanPanel u (imprint P T):= Prod.ext (funext fun n=> funext fun i=>angleD u T (P.1 n) i) (funext fun i=>angleD u T P.2 i)
lemma echoAge (u:D≤l)(P:Single G D)(i:Alma F)(k r): echoS F (leanTex u P k r) i= echoS F (P k r) i:=by
    unfold echoS trellis
    have hh : arret (brow F i l) (leanTex u P k r) h (valence F i)=arret (brow F i D) (P k r) h (valence F i):= by
       unfold arret; apply tsum_congr; intro x; congr 1; change P k r x (portalV u _) = _; unfold brow; rw [portage]; rfl
    rw [hh]
lemma laneπ (u:D≤ l)(P: Thesis F D): prismata F (fun i=>leanTex u (P i))=prismata F P:=by refine extortion fun k i j=>?_; rw [coined,coined]; unfold glean; simp_rw [echoAge]
-- proof both valid if P at incoming Bends; comparison on overlap.
variable {E W C C':Credit}{p:h<D}{p':h<l}{T:SectionData F}
lemma together (L:Theatre H T p e E W)(L':Theatre H T p' a C C')(e:L'.V.draws=L.V.draws)(v:L'.V.paid=L.V.paid)(u:D≤l)(hi:L.V.anchor ≤ m)(hq:L'.V.anchor ≤ m)(w:m≤ N):
     (L'.lore N m:Island F l)=leanPanel u (L.lore N m):=by
    induction w using Nat.decreasingInduction with
    | self=>
       unfold Theatre.lore; rw [Peak_initial,Peak_initial]; refine Prod.ext (funext (fun n=>funext fun i=>?_)) (funext fun i=>?_)
       · ext1 j; funext r x; change herald T p' i _ _ _ _= voteD u (herald T p i n j r x); unfold herald; rw [jewelC i p u, map_smul]
       ext1 j; funext r x; change anthem T p' i j r x= voteD u (anthem T p i j r x); unfold anthem; by_cases v:valence F i+j=r
       · subst r; rw [shine_lit,shine_lit]; unfold carte; rw [jewelC i p u,map_smul]
       rw [shine_dark v,shine_dark v]; exact (map_zero _).symm
    | of_succ i w ih=>
       let A:=L.V.draws; let Ñ:=L.V.paid; let A':=L'.V.draws; let Ñ':=L'.V.paid; let Y:= L.lore N (i+1); let V:= L'.lore N (i+1); let P:= Cosmos.descend A Ñ N i Y; let Q:= Cosmos.descend A' Ñ' N i V; have hg:V=leanPanel u Y:= ih (by omega) (by omega); have he:P.1= P.1:= rfl
       have hY:= (production L (show i+1≤N from w) (by omega)).1.scan; have hV: Chain F Q.1 Q.2:= running A' Ñ' w L'.V.hG L'.V.green (production L' (show i+1≤N from w) (by omega)).1.scan
       have ht : Q.1=(leanPanel u P).1:=by unfold Q; rw [hg,show A'= A from e,show Ñ'=Ñ from v]; exact funext (fun n=> funext (fun j=> apprise A Ñ u (Y.1 (n*(ll A i).L) j) N h))
       have hp : Chain F P.1 P.2 := running A Ñ w L.V.hG L.V.green hY
       have hx: Q=leanPanel u P:= by
          refine Prod.ext ht (funext fun j=>funext fun t=>funext fun k=>?_); have hu: Bends 0 (fun n=> (leanPanel u P).1 n j t k) ((leanPanel u P).2 j t k):= ((hp.solo j).shore t k).touch (voteD u); exact ((ht.symm ▸ hu) : Bends 0 (fun n=>Q.1 n j t k) _).exten ((hV.solo j).shore t k) |>.symm
       rw [show L'.lore N i=reglazed Q from marched _ _ _ _ w, show L.lore N i=reglazed P from marched _ _ _ _ w,hx]; unfold reglazed; rw [show (leanPanel u P).2=(fun i=> leanTex u (P.2 i)) from rfl, laneπ,imprintD]
theorem coequal (L:Theatre H T p e E W)(L':Theatre H T p' a C C')(z:L'.V.draws=L.V.draws)(v:L'.V.paid=L.V.paid)(u:D≤l)(hi:L.V.anchor≤m)(hq:L'.V.anchor≤m)(g:i≤e)(h:i≤a)(j:Alma F): L'.matron m j i= leanTex u (L.matron m j) i:=by
   funext r x; apply tendsto_nhds_unique (gleaming L' hq h j r x); exact ((voteD u).continuous.continuousAt.tendsto.comp (gleaming L hi g j r x)).congr' ((eventually_ge_atTop m).mono (fun n hn=>by dsimp only [Function.comp_apply]; rw [together L L' z v u hi hq (show m≤n from hn)]; rfl))
end YM.WilsonCoeffUV.Cosmos
