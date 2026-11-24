import YM.WilsonCoeffUV.Stable.AllCuts
/-!
# v^mt zeroth-order calibration algebra. Matching residual only through stencil operations.
Full cover Wick covariance. Not Gram nor Lanc.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{V:Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}{T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit} {R S: TowerS G D}
section
variable (A:Levels G)
lemma iceDot (Y:TowerS G D) (P:On k Y)(c:ℝ) (l m N): paveS A m N l (c• Y.2 0)=c• paveS A m N l (Y.2 0):= by
   simpa only [Finset.sum_singleton] using (iceFleet (U:=Unit) (A:=A) (m:=m) (N:=N) (k:=l) (c:=fun _=>c) (X:=fun _=>Y.2) (P:=fun _=>Y.1) {()} (fun i _=> P.shore 0))
lemma icy_minus (p:On k R)(q:On k S)(l m N): paveS A m N l ((R-S).2 0)=paveS A m N l (R.2 0) - paveS A m N l (S.2 0):=by
   let x: Fin 2→ TowerS G D:= ![R,S]; let c:Fin 2 → ℝ:= ![1,-1]; have hp (i:Fin 2):On k (x i):= by fin_cases i; exact p; exact q
   have ht:= iceFleet (A:=A) (m:=m) (N:=N) (k:=l) (X:=fun i=>(x i).2) (P:=fun i=>(x i).1) (c:=c) Finset.univ (fun i _=> (hp i).shore 0)
   rw [Fin.sum_univ_two,Fin.sum_univ_two] at ht; let T:= R.2 0; let U:= S.2 0; change paveS A m N l ((1:ℝ)•T+(-1:ℝ)•U)=(1:ℝ)•_+(-1:ℝ)• paveS A m N l U at ht; rw [one_smul,one_smul,neg_one_smul ℝ U,neg_one_smul ℝ (paveS A m N l U), ←sub_eq_add_neg,←sub_eq_add_neg] at ht; exact ht
lemma clocksW (p:On k R)(q:On k S)(h:k≤l)(i:Alma F)(m N): wickT A m N l F (R-S).2 i= wickT A m N l F R.2 i-wickT A m N l F S.2 i:=by
   unfold wickT; rw [icy_minus A p q]; obtain ⟨x,y,hx,hp⟩:= (winds_carve A _ _ p l h N m (valence F i)).tax; obtain ⟨u,v,hu,hv⟩:= (winds_carve A _ _ q l h N m (valence F i)).tax; exact echo_minus F i hp hv hx hu
lemma WickBase (P:Island F D)(q:Shimmer P)(V:Verse F)(u:h≤k)(m N): wickT A m N k F (Shrine P V).2 = wickM A m N F P.2*ᵥ fun i=> coeff 0 (V i):=by
    let S:= Shrine P V; have hp:still (S.2 0) (h+1):= fun i x=> (solo_shape (Shrine_on P q V (le_refl h))) 0 i (by omega)
    ext1 i; unfold wickT
    rw [show paveS A m N k (S.2 0)=paveS A m N h (S.2 0) from mason_delta k hp u]
    have he: S.2 0=∑ i,(coeff 0 (V i)) • P.2 i 0 := by simp only [S, Shrine,Prod.snd_sum,Stem, affix,Finset.sum_apply,Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; rfl
    change echoS F (paveS A m N h (S.2 0) _) _= _; rw [he,iceFleet (P:=fun i n=>P.1 n i) (X:=fun i=>P.2 i) Finset.univ (fun i _=> (q.scan.solo i).shore 0), Finset.sum_apply, echo_sum]; unfold Matrix.mulVec dotProduct; exact Finset.sum_congr rfl (fun j _=>(echo_mu F i _ _).trans (mul_comm ..))
    exact fun j _ => Standby.μ ((winds_carve A _ _ (q.scan.solo j) h (valence_cap ..) N m _).tax) _
end

variable (L:CutsP H T p v E W K U')
namespace CutsP
-- local at actual m ρ. angular engineering
abbrev LensC (j):= wickT L.ax (L.m+j) L.N k F (L.springP j).2
abbrev lHorizon:= identum (forwardW L.ax L.tx T p L.N L.m L.i)
lemma transit (t:i<L.i): L.LensC i= identum (lineS (Jacob L.ax L.tx T p L.N (L.m+i)) 0) *ᵥ L.LensC (i+1):=by
   let A:=L.ax; let Ñ:=L.tx; let P:=L.springP (i+1); let m:=L.m+i; let X:=P.2; have hp:= L.onward (show i+1≤ L.i from t)
   have ht : m<L.N:= lt_of_lt_of_le (Nat.add_lt_add_left t L.m) (L.hc.trans L.hn)
   have hk:L.vesselsC.anchor≤ m:= L.ha.trans (Nat.le_add_right ..)
   let U:= Spout L.ax L.tx L.N m h k P; let e:=gradeH (ll A m) h k; let T':= lineS (Jacob L.ax L.tx T p L.N m) 0
   have he: L.springP i=U:= (L.carve2 t).symm; funext x; unfold LensC Matrix.mulVec dotProduct; rw [he, show L.m+(i+1)=m+1 by unfold m; omega]; unfold wickT
   let R:= marchT L.ax L.tx L.N m k P.2; let W: TowerS G D:= (fun n=> cloakP A Ñ L.N m k n (P.1 (n*(ll A m).L)),R); have hW : On k W:=by have hx:=ShedG (h:=k) A Ñ ht L.vesselsC.hG L.vesselsC.green hp (le_refl k); unfold Spout at hx; rw [grade_base,one_smul] at hx; exact hx
   let B:=paveS A (m+1) L.N k (P.2 0); let K:= shuttleM (feedA A L.N m); let X' q:=hall (loose A m) h K (B q)
   have hv: paveS A m L.N k (U.2 0)=fun q=> X' q:=by
       rw [show U.2 0=e • W.2 0 from rfl,iceDot A W hW]; change e • paveS A m L.N k (marchT A Ñ L.N m k P.2 0)=_; rw [Carp.descent A Ñ P.2 ht L.vesselsC.hG L.vesselsC.green (solo_shape hp) (On.flanks hp) (solo_stretch hp)]; funext q; rw [Pi.smul_apply]; unfold X' hall; rw [smul_smul,gradeBB]
   rw [hv]; let Y:= L.L.L.lore L.N (m+1); have hg: Shimmer Y:= (production L.L.L ht (by apply hk.trans; omega)).1
   have hh (q:ℕ):Hedged (B q):= winds_carve A X _ hp k le_rfl L.N (m+1) q
   rw [show echoS F (X' (valence F x)) x= ∑ i,identum T' x i*echoS F (B (valence F x)) i from bureau F Y hg H p ht L.vesselsC.hG L.vesselsC.green (L.L.L.effort _ hk) x _ (hh (valence F x))]; refine Finset.sum_congr rfl fun i _=>?_ ; change _*_=identum T' x i *_; by_cases ht:valence F x=valence F i; · apply congr_arg (identum T' x i * ·); rw [ht]
   simp [identum,ht]
lemma lensBridge : L.LensC 0=L.lHorizon *ᵥ L.LensC L.i:=by
   let V:=L.vesselsC; let P k:= forwardW V.draws V.paid T p L.N L.m k
   suffices H: ∀ i≤L.i,L.LensC 0=identum (P i) *ᵥ L.LensC i from H L.i le_rfl
   intro i hi; induction i with
   | zero=> rw [show P 0=1 from junior,ident0,Matrix.one_mulVec]
   | succ i ih=>
      have hv:=wallways L.L.L (m:=L.m) (N:=L.N) L.ha (show L.m+i≤L.N from by have hx:=L.hc.trans L.hn; omega); let Z:= Jacob L.ax L.tx T p L.N (L.m+i)
      have hh:= leaseN L.L.L (m:=L.m+i) (N:=L.N) (L.ha.trans (Nat.le_add_right ..)) (lt_of_lt_of_le (Nat.add_lt_add_left hi L.m) (L.hc.trans L.hn))
      have hg:P (i+1)=P i*lineS Z 0:=by unfold P forwardW; rw [orchestra,line_mul,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,maxStroke]
      have hr: L.LensC i=identum (lineS Z 0)*ᵥ L.LensC (i+1):= L.transit hi
      calc
          _ = identum (P i)*ᵥ L.LensC i:= ih (by omega)
          _ = _ := by rw [hr,hg,identT hv.2.1 hh.1,Matrix.mulVec_mulVec]
lemma topViz (i:Alma F): L.LensC L.i i = wickT L.ax (L.m+L.i) L.N k F L.pt.2 i - (Wray L.ax L.tx T p L.N (L.m+L.i) *ᵥ fun i=> coeff 0 (L.tileP i)) i:=by
    let P:=L.L.L.lore L.N (L.m+L.i); let T:= Shrine L.Ntop L.tileP; have he: Shimmer P:= (production L.L.L (L.hc.trans L.hn) L.reach).1
    change wickT L.ax _ L.N k F (L.springP L.i).2 i= _; rw [carve1,clocksW L.ax L.sp (Shrine_on P he L.tileP v.hk) le_rfl, WickBase L.ax L.Ntop he L.tileP v.hk]
end CutsP
end YM.WilsonCoeffUV.Shard
