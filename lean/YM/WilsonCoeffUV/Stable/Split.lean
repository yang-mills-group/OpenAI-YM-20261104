import YM.WilsonCoeffUV.Stable.Spout
/-! # D sector. Invariant top h stencils arbitrary k+h. -/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Realm PathCost Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c L:Side}{U V:Type*}{r h D l j e k a m u N:ℕ} {G:Gauge}{F:Labels.Frame G h}
abbrev Verse (F:Frame G h):= Alma F→Cost
def opal (F:Frame G h)(Y:TowerS G D): Verse F:= fun i=>PowerSeries.mk fun k=> glean F Y.2 k i
def Stem (c: Cost)(Y:TowerS G D):TowerS G D:=(fun n=>affix c (Y.1 n),affix c Y.2)
def vein (X:Island F D)(i: Alma F): TowerS G D :=(fun n=> X.1 n i,X.2 i)
def Shrine (X:Island F D)(v: Verse F): TowerS G D:= ∑ i,Stem (v i) (vein X i)
lemma On.stem {Y:TowerS G D}(p:On k Y)(a:Cost): On k (Stem a Y):=⟨fun i j=> by simp_rw [Stem,affix,Finset.sum_apply]; exact anzas (P:=fun (k:ℕ×ℕ) n=> coeff k.1 a • Y.1 n k.2 j) _ (fun k _=>(p.shore k.2 j).μ _), fun i=> affix_shell a _ (p.launch i),fun i=>aspire _ _ (p.evenS _),fun n=>incense _ _ _ _ (p.launch n) (p.launch n) (p.oneS n)⟩
lemma hailed (X:Island F D)(h:Shimmer X)(v:Alma F)(p:valence F v≤ k): On k (vein X v):= On.expand (P:=vein X v) (h.scan.solo v) p
lemma Shrine_on (X:Island F D)(t:Shimmer X)(v: Verse F) (hk:h≤k):On k (Shrine X v):= On.sum (fun i _=> (hailed X t i ((valence_cap ..).trans hk)).stem _)
lemma Shrine_img [AddCommGroup U][Module ℝ U]{P:BookC F U V}(T:Coil F)(w:Verse F) : ∑ i,affix (w i) (impose P T i)=∑ i,affix ((T*ᵥ w) i) (P i):=by
    simp_rw [impose,affix_sum,affix_mul]; rw [Finset.sum_comm]; simp_rw [Matrix.mulVec,dotProduct,addend]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by rw [mul_comm]
lemma Shrine_t (X:Island F D)(V: Coil F)(w: Verse F) : Shrine (imprint X V) w= Shrine X (V *ᵥ w):=by
   refine Prod.ext (funext fun n=>?_) ?_; · simp only [Shrine,Prod.fst_sum,Finset.sum_apply]; exact Shrine_img V w
   simp only [Shrine,Prod.snd_sum]; exact Shrine_img V w
lemma Shrine_read(X:Island F D)(v:Verse F)(u:Shimmer X) : opal F (Shrine X v)=v:=by
    have ht : (prismata F X.2) *ᵥ v=v:= by rw [u.era,Matrix.one_mulVec];
    apply funext; intro i; ext1 k; simp only [opal,coeff_mk,Shrine,Prod.snd_sum,glean_pool F i Finset.univ (show ∀ j∈Finset.univ (α:=Alma F),∀u l,Standby ((Stem (v j) (vein X j)).2 u l) from fun j _=> Standby.affixed (solo_stretch (u.scan.solo j)) (v j))]
    nth_rw 2 [←ht];
    simp_rw [Matrix.mulVec,dotProduct,map_sum]; apply Finset.sum_congr rfl; intro b _; unfold Stem vein; dsimp only; rw [glean_stake F _ (solo_stretch (u.scan.solo b)),mul_comm,coeff_mul]; exact Finset.sum_congr rfl fun j _=>congr_arg (coeff j.1 (v b)*·) (coined X.2 j.2 i b).symm
lemma On.read_sub (F:Frame G h){P Q:TowerS G D}(p:On k P)(q:On k Q):opal F (P-Q)=opal F P-opal F Q:=by
    funext i; ext1 j; unfold opal; rw [Pi.sub_apply,map_sub,coeff_mk,coeff_mk,coeff_mk]; exact glean_sub F i (P:=P.2) (Q:=Q.2) fun a _ b _=>by obtain ⟨s,A,h,h'⟩:= solo_stretch p a b; obtain ⟨t,B,v,v'⟩:= solo_stretch q a b; exact ⟨s,t,A,B,h,v,h',v'⟩
-- fields at finite procedure. exact in coupling resets
def music (A:Cost)(v:Verse F): Verse F:=fun i=> Bank.reel A (v i)
variable (A:Levels G)(Ñ:ChartRatio G)
def Spray (_T:SectionData F)(_p:h<D)(N m k:ℕ)(Y:TowerS G D): Verse F:= opal F (Spout A Ñ N m h k Y)
def Sink (T:SectionData F)(p:h<D)(N m k:ℕ)(Y:TowerS G D): TowerS G D:= Spout A Ñ N m h k Y - Shrine (Peaks A Ñ T p N m) (Spray A Ñ T p N m k Y)
omit A Ñ in
lemma Sink_for (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D){P:TowerS G D}(he:Shimmer (Peaks A Ñ T p N m))(hz:h≤k) (hv:m<N)(g:G.Simple)(q:LocalRatio Ñ)(W:On k P): On k (Sink A Ñ T p N m k P) ∧ opal F (Sink A Ñ T p N m k P)=0:=by
    unfold Sink; let Z:= Shrine (Peaks A Ñ T p N m) (Spray A Ñ T p N m k P); have hX:On k (Spout A Ñ N m h k P):=ShedG A Ñ hv g q W le_rfl; have he':On k Z:= Shrine_on _ he _ hz
    refine ⟨hX.diff he',?_⟩; rw [On.read_sub F hX he',Shrine_read _ _ he]; exact sub_self _
lemma resonated (X:TowerS G D)(v:Cost)(u:On k X)(p:m<N)(g:G.Simple)(q:LocalRatio Ñ) : Spout A Ñ N m h k (Stem v X)=Stem (Bank.reel (ratioHigh A Ñ N m) v) (Spout A Ñ N m h k X):=by
   have hh : (Spout A Ñ N m h k (Stem v X)).1=(Stem (Bank.reel (ratioHigh A Ñ N m) v) (Spout A Ñ N m h k X)).1:=by
       funext n; unfold Spout Stem; simp only [Prod.smul_fst,Pi.smul_apply]; rw [affix_μ]; exact congr_arg (gradeH (ll A m) h k • ·) (ropeT A Ñ _ _ g p q (u.launch _) (u.evenS _))
   have hv:= (ShedG A Ñ (h:=h) p g q u le_rfl).stem (Bank.reel (ratioHigh A Ñ N m) v); have ht:= ShedG A Ñ (h:=h) p g q (u.stem v) le_rfl; refine Prod.ext hh (funext fun i=>funext fun j=>?_); apply Soil.Bends.exten (ht.shore i j); exact (hv.shore i j).congr (Eventually.of_forall fun n=> congr_fun (congr_fun (congr_fun hh.symm n) i) j)

lemma emptied {T:SectionData F}{p:h<D}(g:G.Simple)(u:LocalRatio Ñ)(v:m<N)(f:leaseM (loose A m).L F (lineS (Jacob A Ñ T p N m) 0))(X:Verse F)(t:Shimmer (Peaks A Ñ T p N (m+1)))(w:h≤k) : Spout A Ñ N m h k (Shrine (Peaks A Ñ T p N (m+1)) X) = Shrine (Peaks A Ñ T p N m) (Jacob A Ñ T p N m *ᵥ music (ratioHigh A Ñ N m) X) := by
    let J:=Jacob A Ñ T p N m; let W:=Peaks A Ñ T p N m; let V:= Peaks A Ñ T p N (m+1)
    have he: imprint W J=Cosmos.descend A Ñ N m V:=by
        unfold W; rw [marched _ _ _ _ v]; change imprint (imprint _ J⁻¹) J=_; rw [imitive,Matrix.nonsing_inv_mul _ (stellarized f),completeF]
    have ht i : On h (Stem (X i) (vein V i)):= (hailed V t i (valence_cap ..)).stem _
    rw [← Shrine_t W J, he,← saturate A Ñ v g u (Shrine_on V t X le_rfl) le_rfl w]; unfold Shrine
    have hz:=Shed_add A Ñ (X:=fun i=>Stem (X i) (vein V i)) (k:=h) (h:=h) v g u (fun _=>1) ht
    simp_rw [one_smul] at hz; rw [hz]; apply Finset.sum_congr rfl; intro i _; rw [resonated A Ñ (vein V i) _ (hailed V t i (valence_cap ..)) v g u]; unfold Spout; rw [grade_base,one_smul]; rfl
end YM.WilsonCoeffUV.Shard
