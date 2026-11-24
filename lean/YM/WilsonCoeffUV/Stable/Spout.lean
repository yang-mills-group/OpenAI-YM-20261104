import YM.WilsonCoeffUV.Stable.TaylorGain
/-!
# Extend height for invariant & use actions on VOC. Supports k assigned slots plus e, can exceed global h.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c L:Side}{U V:Type*}{r h D l j e k a m u N:ℕ} {G:Gauge}{F:Labels.Frame G h}

abbrev TowerS (G:Gauge)(D:ℕ):= Estate G D × Single G D
abbrev On (k:ℕ)(P: TowerS G D): Prop:= Cosmos.Solo k P.1 P.2
-- arbitrary rank slots. Gauge closure includes orientation 1; rotational polarization preserved at aggregate.
def gradeH (P:Patch) (h k:ℕ):ℝ:= (P.L.val:ℝ)^h/(P.L.val:ℝ)^k
variable (A:Levels G)(Ñ:ChartRatio G)
def Spout (N m h k:ℕ)(P:TowerS G D): TowerS G D:= gradeH (ll A m) h k • ((fun n=> cloakP A Ñ N m k n (P.1 (n*(ll A m).L))), marchT A Ñ N m k P.2)
omit A Ñ in
lemma gradeBB (P:Patch)(h k:ℕ): gradeH P h k *tiara P k=tiara P h:=by unfold gradeH tiara; field_simp
omit A Ñ in
lemma grade_nn (P:Patch)(h k:ℕ):0≤gradeH P h k:= by unfold gradeH; positivity
omit A Ñ in
lemma grade_base (P:Patch)(h:ℕ): gradeH P h h=1:=div_self (by positivity)

omit A Ñ in
lemma portSmooth {P: Pal (Vote D) U}(h:∀ i,Pure (P i))(u:ℝ)(i):Pure ((u•P) i):= by intro r; exact Blue.Smooth.smul (h i r) u
variable {P Q: TowerS G D}
omit A Ñ in
lemma On.μ (p:On k P)(a:ℝ): On k (a•P):=⟨fun i j=>Soil.Bends.μ (p.shore i j) a,fun n=>mu_shellG (p.launch n) a,fun n=>portSmooth (p.evenS n) a,fun n=>swellG (p.oneS n) (p.launch n) (p.launch n) a⟩
omit A Ñ in
lemma On.sum {S:Finset U}{P:U→ TowerS G D}(p:∀ i∈ S,On k (P i)): On k (∑ i∈ S,P i):=by
    have hp n i : Pure ((∑ j∈ S,(P j).1 n) i):=by rw [Finset.sum_apply]; intro v; rw [Finset.sum_apply]; exact Blue.Smooth.sum (fun z a=>(p z a).evenS n i v)
    have ht n: (∑ i∈ S,P i).1 n=∑ i∈ S,(P i).1 n:=by simp only [Prod.fst_sum,Finset.sum_apply];
    have hv i j: Bends 0 (fun n=> (∑ a∈ S,(P a).1 n) i j) ((∑ i∈S,P i).2 i j):=by simp_rw [Prod.snd_sum,Finset.sum_apply]; exact anzas (P:=fun x n=> (P x).1 n i j) S (fun i h=> (p i h).shore ..)
    refine ⟨fun i j=>(hv i j).congr (Eventually.of_forall fun n=>congr_fun (congr_fun (ht n).symm _) _),fun n=> (ht n).symm ▸ shelf (P:=fun i=>(P i).1 n) (fun i hi=>(p i hi).launch n), fun n=>(ht n).symm ▸ (fun i=> hp n i),fun n=>?_⟩
    rw [ht]; exact pulseJ S (fun i hi=> (p i hi).oneS n) (fun i hi=> (p i hi).launch n) (fun i hi=> (p i hi).launch n)
omit A Ñ in
lemma On.add(p:On k P)(q:On k Q): On k (P+Q):=by
   have h (i:Fin 2)(_ :i ∈ Finset.univ):On k (![P,Q] i):=by fin_cases i; exact p; exact q
   simpa [Fin.sum_univ_succ] using On.sum h
omit A Ñ in
lemma On.diff(p:On k P)(q:On k Q): On k (P-Q):= by rw [sub_eq_add_neg,←neg_one_smul ℝ]; exact p.add (q.μ _)
omit A Ñ in lemma On.expand (p:On k P)(h:k≤l):On l P:=⟨p.shore,fun i=>shell_mon (p.launch i) h,p.evenS,p.oneS⟩
omit A Ñ in lemma On.flanks (p:On k P): Stakes P.2:= ⟨fun i=> solo_pure p i,solo_upright p,fun i j=>solo_mural p j i⟩

lemma ShedG {X:TowerS G D}(p:m<N)(g:G.Simple)(q:LocalRatio Ñ)(hX: On k X)(u:k≤l): On k (Spout A Ñ N m h l X):=by
   let K:= ll A m; let t:= (story A Ñ N (m+1)).1; let f:=freeForms A N (m+1); let h:= A.clock.kernel; let L:= roam A N m; let T (n:Side):= t (n*K.L); let V n:= X.1 (n*K.L)
   let R (n):= collarT K h Ñ f L l D (n:=n) (T n) (V n)
   have hx:=old A Ñ g q N (m+1) p
   have ht n: shellK k (R n):= pin_test K h Ñ f L l k q _ _ (hx.basis _).lamp (hX.launch _)
   let b:=ratioHigh A Ñ N m; have hb:constantCoeff b=1:=back_cc (angle_tilt g q p)
   let P:TowerS G D:= (fun n=>mix b (R n), marchT A Ñ N m l X.2)
   refine On.μ (P:=P) ⟨fun i j=>?_,fun n=>mix_length (ht n),fun n j=> mix_pure (P:=R n) (pin_valid K h Ñ f L l _ _ (hX.evenS _)) j,fun n=>?_⟩ _
   · apply whirlB (P:=R); intro i r; exact bells_period K h Ñ f L l (A.blocks m 0).branches q hx.patch (resin A N m p) (U:=X.1) hX.shore i r
   apply wreathe_mix _ (ht n) (ht n) hb; exact bells_act K h Ñ f _ L l q (A.blocks m 0).branches ((cond_laws A m N).1 n (n*K.L) rfl) (horizon_step A m N p n (n*K.L) rfl) (age_sym A ..) _ (hx.basis _) 1 (shell_mon (hX.launch _) u) (shell_mon (hX.launch _) u) (hX.evenS _) (hX.evenS _) (hX.oneS _)

omit A Ñ in
lemma tall_reed (S:StepData n c)(V:Forest S.ratio)(Ñ:ChartRatio G)(H:FaceRow)(Q:Matrix (Body 1 c) (Body 1 n) ℝ)(p:LocalRatio Ñ) (t:PChart G c)(F:Vell G c D)(hT:shellK 2 t)(h:shellK k F)(e:k≤ l)(f:l≤a): reed S V H Q Ñ t l F=reed S V H Q Ñ t a F:=by
   funext i; apply congr_arg (fade plug)
   apply Finset.sum_subset (by apply Finset.range_mono; omega); intro j hj h'; funext r; have hv:=Finset.mem_range.mp hj; have ht:¬j<1+l+3*i:=by simpa only [Finset.mem_range] using h'
   exact srStops S V H Q k hT p h j i r (Or.inr (by omega))
omit A Ñ in
lemma mix_compV {P:Pal (Vote D) U}(c:ℝ){V: Cost}: Blue.mix V (c • P)= c • Blue.mix V P:=by ext1 i; ext1 j; simp only [Pi.smul_apply,Blue.mix,Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=> smul_comm ..
lemma saturate {Y:TowerS G D}(p:m<N)(g:G.Simple)(q:LocalRatio Ñ)(z:On k Y)(e:k≤l)(f:l≤a) : Spout A Ñ N m h l Y=Spout A Ñ N m h a Y:=by
    let R:= Spout A Ñ N m h l Y; let T:= Spout A Ñ N m h a Y; have hp:=ShedG A Ñ (h:=h) p g q z e; have ht:=ShedG A Ñ (h:=h) p g q z (e.trans f)
    have hv: R.1=T.1:=by
       funext n; let U:= ll A m; let K:=A.clock.kernel; let t:= (story A Ñ N (m+1)).1 (n*U.L); let j:=freeForms A N (m+1); let M:= roam A N m; let x:= Y.1 (n*U.L); let b:=ratioHigh A Ñ N m
       change gradeH U h l • Blue.mix b (collarT U K Ñ j M l D (n:=n) t x)= gradeH U h a • Blue.mix b (collarT U K Ñ j M a D (n:=n) t x); rw [← mix_compV, ← mix_compV]; apply congr_arg (Blue.mix b)
       let L w:=bellOne U K Ñ j M l D (n:=n) w t x; let F w:=bellOne U K Ñ j M a D (n:=n) w t x
       change gradeH U h l • (tiara U l • (∑ w,L w))=gradeH U h a •(tiara U a • (∑ w,F w)); rw [smul_smul,smul_smul,gradeBB,gradeBB]; exact congr_arg (tiara U h • ·) (Finset.sum_congr rfl (fun i _=>tall_reed _ _ _ _ _ q _ _ ((old A Ñ g q N (m+1) p).basis (n*U.L)).lamp (gather_mark U x i _ (z.launch _)) e f))
    refine Prod.ext hv (funext fun i=> funext fun j=> (show R.2 i j=T.2 i j from ?_)); have hh:=hp.shore i j; change Bends 0 (fun n=>R.1 n i j) _ at hh; rw [hv] at hh; exact hh.exten (ht.shore i j)
lemma Shed_add {X:U→ TowerS G D}[Fintype U](p:m<N)(g:G.Simple)(q: LocalRatio Ñ) (d:U→ℝ)(hp:∀ i,On k (X i)): Spout A Ñ N m h k (∑ i,d i • X i) = ∑ i,d i • Spout A Ñ N m h k (X i):=by
   let M:= Spout (D:=D) A Ñ N m h k
   have he: (M (∑ i,d i • X i)).1=(∑ i,d i • M (X i)).1:=by
       funext n; let L:= ll A m; let J:= gradeH L h k; simp only [Prod.fst_sum,Finset.sum_apply,Prod.smul_fst,Pi.smul_apply]; change J • cloakP A Ñ N m k n ((∑ i,d i • X i).1 (n*L.L))= _; simp only [Prod.fst_sum,Finset.sum_apply, Prod.smul_fst, Pi.smul_apply]; rw [cloakP_sum,Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=>smul_comm ..)
   have ht:=ShedG A Ñ (h:=h) p g q (On.sum (S:=Finset.univ) (fun i _=>(hp i).μ (d i))) (le_refl k); have hx: On k (∑ i,d i • M (X i)):= On.sum (S:=Finset.univ) (fun i _=> On.μ (ShedG A Ñ p g q (hp i) le_rfl) _); apply Prod.ext he; funext i j; apply Soil.Bends.exten (ht.shore i j); exact (hx.shore i j).congr (Eventually.of_forall fun n=> congr_fun (congr_fun (congr_fun he.symm n) i) j)
lemma Shed_sub(p:m<N)(g:G.Simple)(q:LocalRatio Ñ)(hP:On k P)(hQ:On k Q): Spout A Ñ N m h k (P-Q)=Spout A Ñ N m h k P-Spout A Ñ N m h k Q:=by
   have ht (i:Fin 2) : On k (![P,Q] i):= by fin_cases i; exact hP; exact hQ
   have hx:= Shed_add A Ñ (h:=h) (X:=![P,Q]) p g q ![(1:ℝ),-1] ht
   rw [Fin.sum_univ_two,Fin.sum_univ_two] at hx
   change Spout A Ñ N m h k ((1:ℝ) • P+(-1:ℝ) • Q)=(1:ℝ) • Spout A Ñ N m h k P+(-1:ℝ) • Spout A Ñ N m h k Q at hx; rw [one_smul,one_smul,neg_one_smul ℝ Q,neg_one_smul ℝ (Spout A Ñ N m h k Q),←sub_eq_add_neg,←sub_eq_add_neg] at hx; exact hx
end YM.WilsonCoeffUV.Shard
