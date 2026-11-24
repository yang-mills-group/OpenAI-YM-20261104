import YM.WilsonCoeffUV.Marked.Capture.RootAgreement
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{o:ι}{c:Side}{i j i' j' a e r h N n m b b' l:ℕ}{G:Gauge}{σ τ u g B C x y z ρ:ℝ}{E W V' U':Credit}
lemma small_read (A:Levels G)(L:ChartRatio G)(s:Fin (a+1))(Q:Fin (a+1)→SealR G)(F:Wilt Q)(X:Herit Q)(o: CellR)(y:ℝ)(x:Fin (a+1)→Cover):
    let u:=paceT A.S m N; let T:=polarP A L (Q s).ans (Q s).path N m N (X s)
    readO (lyra u y o F x) (coatA A L N m Q X x {s}) c = flash ((locale o (shoe T (F s) u y (x s))).1 c):=by
    intro u T; rw [coatLeaf]; apply congr_arg flash; funext i j z; exact petal_hit (fun i=>(Q i).D) s _ _

lemma embodied (s:Finset ι){w:ι→ ℝ}{X:ι→Era G ℝ}(h:∀ i∈s,Auth l (X i)): flash ((∑ i∈s,w i • X i).1 c)= ∑ i∈s,w i • flash ((X i).1 c):=by
    rw [Prod.fst_sum,Finset.sum_apply]; simp only [Prod.smul_fst, Pi.smul_apply]; rw [flash_term _ (fun i p=>mu_shellG ((h i p).span _) _)]; exact Finset.sum_congr rfl fun i p=>flash_mu _ ((h i p).span _)
lemma poly_agate (n:ℕ)(X:Fin (n+1)→ Era G ℝ)(h:Fin (n+1)→ℕ)(p:∀ i,Auth (h i) (X i)) : flash ((MassP G ℝ n X).1 c) = ∏ i,flash ((X i).1 c):=by
   induction n with
   | zero=>rw [Fin.prod_univ_succ,Fintype.prod_empty,mul_one]; rfl
   | succ n ih=> rw [MassP,Fin.prod_univ_succ]; let L:=MassP G ℝ n (Fin.tail X); have ht i:Auth (Fin.tail h i) (Fin.tail X i):= p i.succ
                 rw [show (agateV (X 0) L).1 c=_ from rfl,show flash ((agateV (X 0) L).1 c) =_ from woadap _ _ (finite_shell ((p 0).span _)) (finite_shell ((manCo _ (Fin.tail h) ht).span _)), ih (Fin.tail X) _ ht]; rfl
lemma smulk [Fintype ι](x:ι→ℝ)(R:ι→ Ink U): (∏ i,x i) • (∏ i,R i)=∏ i,x i • R i:=by simp only [Algebra.smul_def,map_prod, Finset.prod_mul_distrib]

lemma sourceBoot (A: Realm G (e+1) E)(H:Hol G)(Q:Fin (a+1)→SealR G)(P:Tribe A H W V' Q)(q:A.anchor≤ m)(v:m≤ N)(X:Herit Q)(F:Wilt Q)(z:CellR)(y:ℝ):
    let T:=A.draws; let L:=A.paid; let θ:=paceT T.S m N
    Finale θ y z F (asp Q) (AuthSum (coatA T L N m Q X))=locale z (HearthC Q T L F X m N N y) :=by
    intro T L θ; let p:= coatA T L N m Q X; have hv:= cloister P X q v; let D (i):=(Q i).D; let ℐ:=Fin (a+1); let M:= AuthSum p
    have hb i: On (asp Q i) (polarP T L (Q i).ans (Q i).path N m N (X i)):= by
       let K:=(P i).prest; unfold T L; rw [←K.lands,←K.modes]; exact tournure K.f.arch _ (K.tap.symm ▸ (q.trans v)) le_rfl
    have hM:Solo (asp Q) M:= fun i=> placedO _ (hv.level' i)
    apply Auth.ext (Finale_Auth θ y z F _ M hM) (locale_val (HearthC Q T L F X m N N y) (Hearth_enter (fun i=> Nonempty.intro (P i).prest) F X (q.trans v) le_rfl) z)
    funext n; apply by_flash ((Finale_Auth θ y z F _ M hM).span n) ((locale_val _ (Hearth_enter (fun i=>Nonempty.intro (P i).prest) F X (q.trans v) le_rfl) z).span n) ((Finale_Auth θ y z F _ M hM).pale n) ((locale_val _ (Hearth_enter (fun i=>Nonempty.intro (P i).prest) F X (q.trans v) le_rfl) z).pale n);
    let S i:= polarP T L (Q i).ans (Q i).path N m N (X i); let H i (u:Cover):= shoe (S i) (F i) θ y u
    let R:= boxes θ y F; let Z i(u:Cover):= locale z (H i u); let Y i:=locale z ((Q i).spins T L (F i) m N N y (X i));
    have hY i: Auth (asp Q i) (Y i):= locale_val _ (Mer.placed _ (F i) (hb i) θ y) _
    have he i u: Auth (asp Q i) (Z i u):= locale_val _ (((On_auth (hb i)).tuft _).shifted _) _
    have hf i: flash ((Y i).1 n)=∑ u∈ canvasM (F i) θ y,drumB (asp Q i) θ • flash ((Z i u).1 n):=by
        let J:=canvasM (F i) θ y; rw [show Y i= locale z (∑ u∈J,drumB (asp Q i) θ • H i u) from rfl,shoreSum]; exact embodied J fun x _=> he i x
    rw [show locale z (HearthC Q T L F X m N N y)=MassP G ℝ a Y from PortalHome ..,poly_agate a Y (asp Q) hY]; simp_rw [hf]; unfold Finale; rw [embodied R (X:=scrollR θ y z F M) (w:=fun _=> lyric θ (asp Q)) (fun i _=> Auth.tuft (hM _ _) (touch (lyra θ y z F i) Finset.univ)), Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun i hi=>?_ ; let A:=lyra θ y z F i; change (∏ i, drumB _ _) • feeble (M i) A n Finset.univ= _; rw [show feeble _ _ _= _ from firstExp (levels_exp (p i) (hv.level' i) (hv.quiet' i) A n) (show ∀ S:Finset ℐ, S.card≠1→feeble (p i) A n S=0 from fun x h=>by unfold feeble p; rw [coatLazy _ _ _ _ _ _ _ x h,read_emp])]; rw [smulk]; exact Finset.prod_congr rfl fun j _=> congr_arg (drumB (asp Q j) θ • ·) (small_read T L j Q F X z y i)
-- hence actual *formal* report replaces exactly
lemma close_eq (A: Realm G (e+1) E)(H:Hol G)(Q:Fin (a+1)→SealR G)(P:Tribe A H W V' Q)(q:A.anchor≤ m)(v:m≤ N)(X:Herit Q)(F:Wilt Q)(z:CellR)(y:ℝ)(h:b≤m)(x:∀ i j,i≠j→ ClearDay (F i) (F j) (ρ+14)):
     let θ:=paceT A.draws.S m b; let U:=outset A m N ρ (asp Q) (asp Q) (coatA A.draws A.paid N m Q X)
     Finale θ y z F (asp Q) (AuthSum (Gears A.draws A.paid (asp Q) (asp Q) N m b U))= locale z (LodeStar A.draws A.paid F X m b N y) :=by
    intro θ V; unfold V outset θ; rw [reopening A.draws A.paid F _ m b N (cloister P X q v) A.hG A.green h v z x, sourceBoot A H Q P q v X F z y]; exact (cruiseT (century z) A.draws (h.trans v) A.hG A.green le_rfl (Hearth_enter (fun i=>Nonempty.intro (P i).prest) F X (q.trans v) le_rfl)).symm
end YM.WilsonCoeffUV.Wheel.Flooring
