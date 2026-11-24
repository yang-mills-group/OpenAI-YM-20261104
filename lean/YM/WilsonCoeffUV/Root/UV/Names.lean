import YM.WilsonCoeffUV.Root.UV.RingNaturality
/-!
# Recover coarser-to-finer names from one graph output. Quotient not modded.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{p:h<D}
lemma completeF (Y:Island F D): imprint Y 1=Y:= Prod.ext (funext fun _=>impose_plain _) (impose_plain _)
lemma imitive (Y:Island F D)(V X:Coil F): imprint (imprint Y V) X=imprint Y (V*X):= Prod.ext (funext fun n=> imposition V X (Y.1 n)) (imposition V X Y.2)
noncomputable def walkY (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ) (k:ℕ)(Y:Island F D) : Island F D:= match k with | 0 => Y | k+1=> Cosmos.descend A Ñ N m (walkY A Ñ N (m+1) k Y)
variable (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)
omit A Ñ N m in
lemma split_hill (P:ℕ→ Coil F)(k:ℕ): hillcrest P (k+1)= P 0 * hillcrest (fun i=> P (1+i)) k:=by
    induction k with
    | zero=> simp [hillcrest]
    | succ k ih=> rw [hillcrest,ih]; rw [hillcrest,Matrix.mul_assoc, Nat.add_comm 1]
omit A Ñ N m in
lemma hills_loom (P Q:ℕ→ Coil F)(h:Coil F→+* Coil F)(k:ℕ)(u:∀ j<k,Q j=h (P j)): hillcrest Q k=h (hillcrest P k):=by
    induction k with
    | zero=> simp [hillcrest]
    | succ k ih=> rw [hillcrest,hillcrest,ih (fun i hi=>u i (by omega)),u k k.lt_succ_self,map_mul]
omit A Ñ N m in lemma stageChar (A B:Cost)(P:Coil F): Chars F A (Chars F B P)=Chars F (chartB B A) P:=by ext1 i j; exact DFunLike.congr_fun (reel_chart B A) (P i j)
omit A Ñ N m in lemma Chars.one (P:Coil F): Chars F 1 P=P:= Matrix.ext (fun i j=>reel_one (P i j))
lemma roll1 (T: SectionData F)(p:h<D)(k:ℕ): CurNames A Ñ T p N m (k+1) false=Jacob A Ñ T p N m* Chars F (ratioHigh A Ñ N m) (CurNames A Ñ T p N (m+1) k false) :=by
    unfold CurNames; rw [split_hill, show aftGear A Ñ T p N m (k+1) false 0=Jacob A Ñ T p N m from (show Chars F (relativeF A Ñ N m 0) _= _ from Chars.one _)]
    apply congr_arg (Jacob A Ñ T p N m* ·)
    apply hills_loom; intro j _; unfold aftGear warp; simp only [Bool.false_eq_true,↓reduceIte]; rw [stageChar,stageF,Nat.add_assoc m, show relativeF A Ñ N m 1=ratioHigh A Ñ N m from by unfold relativeF; rw [palmB,palmB,chart_one,Nat.add_zero]]

variable {A Ñ N m}
variable {E W:Credit}{T:SectionData F}(L:Theatre H T p e E W)
lemma prang (u:L.V.anchor≤m)(v:m+k≤N) (A: Coil F):
    walkY L.V.draws L.V.paid N m k (imprint (Peaks L.V.draws L.V.paid T p N (m+k)) A)= imprint (Peaks L.V.draws L.V.paid T p N m) (CurNames L.V.draws L.V.paid T p N m k false * Chars F (relativeF L.V.draws L.V.paid N m k) A):=by
    induction k generalizing m with
    | zero=> simp only [walkY,CurNames,hillcrest,Nat.add_zero,relativeF,palmB,Chars.one,_root_.one_mul]
    | succ k ih=>
       let V:= L.V; let X:= L.lore N m; let C:= CurNames V.draws V.paid T p N m; let Y:= L.lore N (m+1); let B:= Cosmos.descend V.draws V.paid N m Y; let M:= Jacob V.draws V.paid T p N m
       have he:m<N:=by omega
       have hh : imprint X M=B:=by
           rw [show X=imprint B M⁻¹ from marched _ _ _ _ he, imitive,Matrix.nonsing_inv_mul M (stellarized (leaseN L u he)),completeF]
       rw [walkY, show m+(k+1)= (m+1)+k by omega,ih (by omega) (by omega), bender _ _ _ (production L (show m+1≤N from by omega) (by omega)).1.scan L.V.hG he L.V.green];
       rw [show Cosmos.descend _ _ _ _ _= _ from hh.symm, imitive,(roll1 L.V.draws L.V.paid N m T p k),map_mul,stageChar,Matrix.mul_assoc]; rw [show relativeF L.V.draws L.V.paid N m (k+1)=relativeF V.draws V.paid N m (1+k) from congr_arg (relativeF V.draws V.paid N m) (Nat.add_comm k 1)]; rw [stageF,show relativeF V.draws V.paid N m 1=ratioHigh V.draws V.paid N m from by unfold relativeF; rw [palmB,palmB,chart_one,Nat.add_zero m]]
lemma compatibleN (u:L.V.anchor≤m)(v:m+k≤N):
    walkY L.V.draws L.V.paid N m k (L.lore N (m+k))=imprint (L.lore N m) (CurNames L.V.draws L.V.paid T p N m k false):= by
    have hp:=prang L (N:=N) (k:=k) u v (1:Coil F); rw [completeF,map_one,_root_.mul_one] at hp; exact hp
lemma cornea (u:L.V.anchor≤ m)(v:m+k≤ N):
    prismata F (walkY L.V.draws L.V.paid N m k (L.lore N (m+k))).2=CurNames L.V.draws L.V.paid T p N m k false:= by
    let H:= (production L v (m:=m+k) (by omega)).1
    have ht: Shimmer (L.lore N m):= (production L (by omega) u).1; rw [compatibleN L u v]; dsimp only [imprint]; rw [prismata_bind F _ (fun i=>solo_stretch (ht.scan.solo i)), ht.era,_root_.one_mul]
lemma swayC (_q:L.V.anchor≤m)(v:m+k≤N):
    Chars F (relativeF L.V.draws L.V.paid N m k) (CurNames L.V.draws L.V.paid T p N m k true) = CurNames L.V.draws L.V.paid T p N m k false:= by
    let A:=L.V.draws; let B:=L.V.paid; let C:=Chars F (relativeF A B N m k)
    symm; apply hills_loom; intro i e; unfold aftGear warp; simp only [Bool.false_eq_true,↓reduceIte]; rw [stageChar]
    let t:=relativeF A B N (m+i) (k-i); let s:=relativeC A B N (m+i) (k-i); let x:=relativeF A B N m i
    have hx: chartB s t=1:=by exact (direction L.V.hG L.V.green (show m+i+(k-i)≤N from by omega)).2
    have ht : relativeF A B N m k=chartB t x:=by
       nth_rw 1 [show k=i+(k-i) by omega]; exact stageF ..
    rw [show chartB _ (relativeF L.V.draws L.V.paid N m k)= x from (show chartB s _= _ from (by rw [ht,←chart_assoc,hx,chart_ones]))]
end YM.WilsonCoeffUV.Cosmos
