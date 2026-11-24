import YM.OPE.Compatible.Glim.Ruff
/-! # VolForce budget -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J:Type}{n:Side}
variable {u t:ℝ}
def bench(n:Side)(x:Site n)(e:RootEdge)(a:G.ColorIndex): Tab (Shade G) n:= ( x + wrap n e.1,e.2,a)
lemma boardHere (i j:G.ColorIndex): ((Phone G).coord i) ((Phone G) j) = (if i=j then 1 else 0):=by simp
noncomputable abbrev functorE (x:Site n)(e:RootEdge)(a:G.ColorIndex):Bid.Dir G n:= An (sett n x e) (Phone G) a
lemma topHere (x:Site n)(e:RootEdge)(i:G.ColorIndex): spool G n (functorE x e i)= deltaH (bench n x e i):=by
   funext ⟨p,j,a⟩; change (((functorE x e i) (whiz (p,j))) a)= _; let v:= placed n x e; by_cases hh:(p,j)=v
   · rw [hh, show functorE x e i (whiz v) = Phone G i from ?_ ,← phone_eq,boardHere a i]; rotate_left; · unfold functorE An; simp only[sett]; simp [v]
     by_cases h:a=i
     · subst i; erw [show (p,j,a)=bench n x e a from congr_arg (fun x:edgeV n=>(x.1,x.2,a)) hh]; simp[deltaH]
     have hP:(p,j,a)≠bench n x e i:=by intro H; exact h (congr_arg (fun i:Tab (Shade G) n=> i.2.2) H)
     simp[deltaH,h,hP]
   have he:(p,j,a)≠bench n x e i:=fun hv=>hh (congr_arg (fun i:Tab (Shade G) n=> (i.1,i.2.1)) hv)
   rw [show functorE x e i (whiz (p,j))=0 from ?_]; simp [deltaH,he]
   unfold functorE An; have hp:whiz (p,j)≠ sett n x e:=fun H=> hh ((driftB n).injective H); simp [hp]
lemma unitWallet (I:Type) [DecidableEq I]: Whole (unitRow I):=⟨1,1,one_pos,fun _ _=> Work.F08.strip_unit ..⟩
lemma drawKey (p:Script (Shade G) (r+1))(v:deck (Shade G) n)(x y:Site n)(e:RootEdge)(i:G.ColorIndex):
    let T:= Fin.cons (deltaH (bench n x e i)) (fun _:Fin r=>v)
    drawP (1:Matrix (Tab (Shade G) n) (Tab (Shade G) n) ℝ) (r:=0) (punch e i) p (fun _=>v) (fun _=>v) x y= scribe y p T:=by
     intro T; let q:= bench n x e i; have he(j:Tab (Shade G) n):scribe x (punch e i) (Fin.cons (deltaH j) (fun _:Fin 0=>v))=deltaH j q:=by
          unfold scribe punch; let W:Page (Shade G) 1:=fun _=>(e.1,e.2,i); rw [tsum_eq_single W]; simp [W,render,q,bench]; intro b hb; rw [Pi.single_eq_of_ne hb,zero_mul]
     unfold drawP; simp_rw [he]; rw [sum_eq_single q]; rotate_left; · intro b hb hp; apply sum_eq_zero; intro j hj; simp [deltaH,hp]
     · simp
     rw [sum_eq_single q]; · rw [Matrix.one_apply_eq, show deltaH q q=1 from (by simp[deltaH]), one_mul,one_mul]
     · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj),zero_mul,zero_mul]
     simp
lemma DrawRead (p:Script (Shade G) (r+1))(h:Summable p)(x:Site n)(e:RootEdge)(i:G.ColorIndex)(v:Bid.Dir G n):library n p (spool G n ∘Fin.cons (functorE x e i) (fun _=>v))=Flume.Script.value x (cotton (unitRow _) (r:=0) (punch e i) p) (spool G n v):=by
     let P:=spool G n v; have ht:=readCotton (d:=r) (p:=punch e i) (q:=p) (r:=0) (unitWallet _) (sootS (bread e i 0)) h (fun _:Fin 0=>P) (fun _:Fin r=>P) x; unfold Flume.Script.value; erw [← show Fin.append (fun _:Fin 0=> P) (fun _:Fin r=>P)=fun _=>spool G n v from funext fun i=>by refine Fin.addCases ?_ (fun i=>?_) i; intro j;exact j.elim0; rw [Fin.append_right]]; refine Eq.trans ?_ ht.symm; rw [acts_unit n]; unfold library; apply Finset.sum_congr rfl; intro j _; rw [drawKey]; apply congr_arg; ext1 k; refine Fin.cases ?_ (fun k=>?_) k; exact topHere x e i; rfl
end YM.OPE.Variance
