import YM.WilsonCoeffUV.Stable.Arrival
/-!
# Charged matching arrangement

Only inverse products, endpoints in native coupling; operator equality
on closed inputs NOT an equality after mask. -/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}

variable (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)

def lay (N m:ℕ)(v:Verse F): Verse F:=Jacob A Ñ T p N m *ᵥ music (ratioHigh A Ñ N m) v
def street (N m i:ℕ)(v:Verse F): Verse F:= CurNames A Ñ T p N m i false *ᵥ music (relativeF A Ñ N m i) v
def steep (N m i:ℕ)(v:Verse F): Verse F:= music (relativeC A Ñ N m i) (bindingS A Ñ T p N m i false *ᵥ v)
def barley (N k c:ℕ) (X:TowerS G D) (i:ℕ) : Verse F:= Spray A Ñ T p N i k (breaths A Ñ T p N k c (i+1) X)
def boot (N k c m i:ℕ)(X:TowerS G D):Verse F:= ∑ j∈Finset.range i, steep A Ñ T p N (m+j) (i-j) (barley A Ñ T p N k c X (m+j))
def burden (N k c m i:ℕ)(X:TowerS G D): TowerS G D:= breaths A Ñ T p N k c (m+i) X - Shrine (Peaks A Ñ T p N (m+i)) (boot A Ñ T p N k c m i X)
lemma musicSum (U:Type*) (S:Finset U){X:U→Verse F}(P:Cost): music P (∑ i∈S,X i)=∑ i∈S,music P (X i):=by funext i; rw [music,Finset.sum_apply,Finset.sum_apply,map_sum]; rfl
lemma lays (U:Type*)(S:Finset U){X:U→Verse F} : lay A Ñ T p N m (∑ i∈S,X i)=∑ i∈S,lay A Ñ T p N m (X i):=by
   unfold lay; rw [musicSum]; ext1 j; simp_rw [Matrix.mulVec,dotProduct,Finset.sum_apply,Finset.mul_sum]; exact Finset.sum_comm
lemma CurN (X P:ℕ→ Coil F)(p:∀ i<k,X i=P i): hillcrest X k=hillcrest P k:=Eq.symm (hills_loom X P (RingHom.id _) k (fun i h=> (p i h).symm))
lemma orchestra : CurNames A Ñ T p N m (i+1) false=CurNames A Ñ T p N m i false * Chars F (relativeF A Ñ N m i) (Jacob A Ñ T p N (m+i)):=by
   unfold CurNames; rw [hillcrest, CurN _ (aftGear A Ñ T p N m i false) (fun _ _=>rfl)]; rfl
lemma joinVerse (C D: Cost)(P:Verse F): music C (music D P)=music (chartB D C) P:= funext fun i=> DFunLike.congr_fun (reel_chart D C) (P i)
lemma musical (P:Verse F): music 1 P=P:=funext fun _=> reel_one _
lemma turnV (P: Verse F)(A:Coil F)(C:Cost): music C (A *ᵥ P)= Chars F C A *ᵥ music C P:=by funext i; unfold Matrix.mulVec music dotProduct; rw [map_sum]; exact Finset.sum_congr rfl fun i _=>map_mul ..
lemma Street_steal (v:Verse F): street A Ñ T p N m i (lay A Ñ T p N (m+i) v)=street A Ñ T p N m (i+1) v:=by
   unfold lay street; rw [orchestra,turnV, joinVerse,Matrix.mulVec_mulVec]; have h2:relativeF A Ñ N m (i+1)=chartB (ratioHigh A Ñ N (m+i)) (relativeF A Ñ N m i):=by rw [relativeF,palmB]; rfl
   rw [←h2]
lemma street_nil (y:Verse F):street A Ñ T p N m 0 y=y:=by unfold street CurNames hillcrest relativeF palmB; rw [musical,Matrix.one_mulVec]
lemma Shrine_zero (P:Island F D): Shrine P 0=0:=by unfold Shrine; apply Finset.sum_eq_zero; intro i _; let B:=vein P i; change Stem 0 B=0; exact Prod.ext (funext fun n=> no_tariff (B.1 n)) (no_tariff B.2)
variable {A Ñ T p} {E W K:Credit} (L:Theatre H T p e E W) {v:Verse F}
lemma street_up (u:L.V.anchor≤m)(q:m+i≤ N): Injective (street L.V.draws L.V.paid T p N m i):=by
    obtain ⟨hv,v⟩:= ebbing L u q false
    have ht: Function.LeftInverse (steep L.V.draws L.V.paid T p N m i) (street L.V.draws L.V.paid T p N m i):=by intro x; unfold steep street; rw [v,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hv, Matrix.one_mulVec, joinVerse, (direction L.V.hG L.V.green q).1,musical]
    exact ht.injective
lemma Street_up (X:Verse F)(u:L.V.anchor≤m)(q:m+i≤N) : street L.V.draws L.V.paid T p N m i (steep L.V.draws L.V.paid T p N m i X)=X:=by
    obtain ⟨hv,h⟩:= ebbing L u q false; unfold street steep; rw [joinVerse, (direction L.V.hG L.V.green q).2,musical,h, Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hv, Matrix.one_mulVec]
lemma steep_height (X:Verse F) (u:L.V.anchor≤m)(q:m+(i+1)≤N):
    let A:=L.V.draws; let Ñ:=L.V.paid; lay A Ñ T p N (m+i) (steep A Ñ T p N m (i+1) X)=steep A Ñ T p N m i X:=by
    intro A Ñ; apply street_up L (m:=m) (i:=i) (N:=N) u (by omega); change street A Ñ T p N m i _=street L.V.draws L.V.paid T p N m i _; rw [Street_steal]; exact (Street_up L X u q).trans (Street_up L X u (show m+i≤N from by omega)).symm
lemma lay_boot (u:L.V.anchor≤m)(q:m+(i+1)≤N)(X:TowerS G D): let A:=L.V.draws; let Ñ:=L.V.paid; lay A Ñ T p N (m+i) (boot A Ñ T p N k c m (i+1) X) = boot A Ñ T p N k c m i X+barley A Ñ T p N k c X (m+i):=by
    intro A Ñ; let T':=barley A Ñ T p N k c X
    have ht j (hj:j∈Finset.range i): lay A Ñ T p N (m+i) (steep A Ñ T p N (m+j) (i+1-j) (T' (m+j))) = steep A Ñ T p N (m+j) (i-j) (T' (m+j)):=by
       have he:= Finset.mem_range.mp hj; have hp': m+i=m+j+(i-j):=by omega
       rw [Nat.succ_sub (by omega),hp']; exact steep_height L _ (by omega) (by omega)
    have he: lay A Ñ T p N (m+i) (steep A Ñ T p N (m+i) 1 (T' (m+i)))=T' (m+i):=by
       let x:=T' (m+i); let B:= steep A Ñ T p N (m+i) 1 x; have hx:lay A Ñ T p N (m+i) B=street A Ñ T p N (m+i) 1 B:= by rw [←Street_steal (m:=m+i) (i:=0),street_nil,Nat.add_zero]
       rw [hx]; exact Street_up L x (by omega) (by omega)
    unfold boot; rw [lays,Finset.sum_range_succ,Finset.sum_congr rfl ht, show i+1-i=1 by omega,he]
variable {v':Rails h k u e}
omit L in
lemma tired (t:Torch H T p v' E W K)(u:t.L.V.anchor ≤ m)(w:m+(i+1) ≤ c)(y:c ≤ N)(X:TowerS G D)(z:On k X)(x:opal F X=0): let L:=t.L; let A:= L.V.draws; let Ñ:= L.V.paid; Spout A Ñ N (m+i) h k (burden A Ñ T p N k c m (i+1) X) = burden A Ñ T p N k c m i X:=by
    intro L A Ñ; let j:=m+i; let I:=L.lore N (j+1); let V:=boot A Ñ T p N k c m (i+1) X; let W:= boot A Ñ T p N k c m i X
    let P:= breaths A Ñ T p N k c (j+1) X; have hP:On k P:= (nursing t (m:=j+1) (by unfold j; omega) (by unfold j; omega) y z x).1
    have hv:j<c:=by unfold j; omega
    have hg:j<N:=hv.trans_le y
    have hL:t.L.V.anchor≤ j:=by unfold j; omega
    have hr:Shimmer I:= (production t.L hg (by omega)).1
    unfold burden; rw [show m+(i+1)=j+1 from by unfold j; omega,Shed_sub _ _ hg L.V.hG L.V.green hP (Shrine_on I hr V v'.hk),emptied _ _ L.V.hG L.V.green hg (leaseN L hL hg) _ hr v'.hk]; let Q:= L.lore N j; let Z:= barley A Ñ T p N k c X j
    rw [show Jacob _ _ _ _ _ _*ᵥ music _ _= W+Z from lay_boot t.L u (w.trans y) X,breath_step A Ñ T p _ hv]
    rw [show Shrine (Peaks _ _ _ _ _ _) (W+Z)= Shrine Q W+ Shrine Q Z from (by
       have he:= Shrine_diff Q (W+Z) W; rw [add_sub_cancel_left] at he; rw [show Shrine Q Z=_ from he]; abel)]
    unfold Sink; change _= _ - Shrine Q Z-Shrine Q W; abel
end YM.WilsonCoeffUV.Shard
