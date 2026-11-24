import YM.OPE.Compatible.Vino.Verd
/-!
# Registration T0 from moving boosts. τ from finite power
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
lemma wagons (P:Flight i j)(H:Mag i j)(K:KernelChoices)(p:Seat d m (Shade G))(h:p∈bed G d m)(hz:f.val=c.val*P.L.val) (s:Site c):
     let S:=P.visit (c:=c) (f:=f) K hz; let M:=Master (G:=G) S P.odd (P.duo K.penalty).A0
     formSong m d G s (wagon P H.2.1 K G d m p)=pulling M (formSong m d G (S.ratio.embed s) p):=by
          intro S M; funext k; ext1 u; change formSong _ _ G _ _ _ _= formSong _ _ _ _ p k (fun i=>M*ᵥu i); rw [tensors,tensors,stool]; exact pipeSpace P H.2.1 K hz u _ (sootS ((sproutV m d p).2 k)) (merit h k).1 s
noncomputable abbrev warmEat (p:Seat k m I)(x:RowB I):= boostS x (-(1/2)) m k p
-- m implicit! ensure m binder input explicit
lemma fealty (P:Flight i j)(H:Mag i j)(hz:f.val=c.val*P.L.val) (p: Phase)(d:ℕ)(m:ℕ) (Q:Seat (d+p.val) (m+1) (Shade G))(hp: Q∈bed G (d+p.val) (m+1)) (A:Alps K T i v) (R:ChartRatio G)(ht:LocalRatio R)(X:Medal P.patch G K.K i) (hA:A.gear=P.wing)(b:ℝ) (s:Site c) (x:Bid.Dir G c):
    let S:=P.visit (c:=c) (f:=f) K.K hz; let W:=forest S.ratio P.odd; let U:Boxes G P.patch K.K:=⟨i,H.1,X,A.gear⟩; let M:= installed S.ratio (P.duo K.K.penalty).A0
    let B:=d+p.val; let n:=m+1; let q:= warmEat (m:=m+1) Q (pointAt G A.gear H.1 K.K f); let w:=warmEat (m:=m+1) (wagon P H.2.1 K.K G B n Q) (pointAt G P.land H.2.1 K.K c)
    ∀ (g:Bid.Dir G c→AxisChart G W)(t:S.Choices), licensed S P.odd U A.clip A.live M A.sky g→ ∀ Y:FibreRep S P.odd U t A g b,
       (TracePay S P.odd U A t g R d (impulse p (lilies n B _ q)) _ s Y x).seq p.val= Flair (lilies n B _ w) B (spool G c x) s:=by
          intro S W U M B n q w g t hl Y
          have h1:= (rentBase P hz K T H b v A hA X g t hl Y (formSong n B G (S.ratio.embed s) Q) (pell hp _) (fun i=>reserves Q A.gear H.1 i (S.ratio.embed s) (merit hp i).1) x); let q' := TracePay S P.odd U A t g R d (impulse p (lilies n B _ q)) _ s Y x
          let L: AxisChart G W→ Bid.Dir G f := fun i=> dressedF A S P.odd t U g Y x i; rw [show q'.seq p.val=_ from (helmQ A R S _ t U g s x Y _ _ p n d (sproutV n _ q) ht).2]; change Y.L.Q.average (Chart.tangent G W.Free) (fun i=>Flair (lilies n B _ q) B (spool G f (L i)) (S.ratio.embed s))=_; simp_rw [← strikesT (m:=n) (k:=B)]; rw [show formSong n B G (S.ratio.embed s) q=_ from finHeat (L:=K.K) Q A.gear H.1 (S.ratio.embed s) _ _,show formSong n B G s w= _ from finHeat (m:=n) (L:=K.K) (wagon P H.2.1 K.K G B n Q) P.land H.2.1 s _ _,wagons P H K.K Q hp hz s]; exact h1

end YM.OPE.Silt.Float
