import YM.OPE.Compatible.Glim.Gale
/-! # EOM roll through two positive. -/
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
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}(e:RootEdge)(b:Bool)
variable {K:Sponsor G}{T:Seasons K}{V:M→ℝ}(A:(j:M)→Alps K T i (V j))
noncomputable abbrev capQ (j:M)(n:Side):= Dune (A j) (n:=n)
variable (u:G.ColorIndex)
abbrev ZTheta {M:Type}(V:M→ℝ):= 1+V
lemma readyK {p:Clip}(h:∀ i,(A i).clip=p): Shut 1 (fun i n x=>Pry (functorE x e u) (Pawn.mold (capQ A i n) 2)) 1 m:=by
     have he(r:ℕ): Take (Z:=M) 1 (fun i n x y=> fderiv ℝ (jet (capQ A i n) (r+1)) y (functorE x e u)) r m:=by
          obtain ⟨c,hc,H⟩:=Alps.word_cost K T i (r+1) m p; apply NeedV e u c hc (P:=fun i=>(A i).word (r+1)) ?_ ?_ ?_; rotate_left
          · intro i n; exact (((A i).fullK r).plot n).sub contDiffAt_const -- sub uses comp ∞
          · intro i n y; unfold capQ Dune; rw[iteratedFDeriv_sub_apply (show ContDiffAt ℝ _ (frameD (A i)) 0 from (((A i).fullK r).plot n).of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,sub_zero]; exact ((A i).fullK (r+1)).wink n _ le_rfl y
          intro s; rw [Pi.one_apply,mul_one]; exact H _ _ (h s)
     intro j; fin_cases j<;>first |exact he 1|exact he 2|exact he 3
lemma readyY (h:0 ≤ V) : Shut (ZTheta V) (fun i n x=> Pry (functorE x e u) (Pawn.mold (Rh (A i) (n:=n)) 0)) 0 m:=by
     have he(r:ℕ): Take V (fun i n x v=> fderiv ℝ (jet (Rh (A i) (n:=n)) (r+1)) v (functorE x e u)) r m:=by
           obtain ⟨c,hc,H⟩:=Alps.leaf_cash K T i (r+1) m; exact NeedV e u c hc (P:=fun i=>(A i).liftZ (r+1)) (fun i=>H _ (h i) (A i)) (fun i n=> ((A i).fullL (r+1)).plot n) (fun i n y=> ((A i).fullL (r+1)).wink n _ le_rfl y)
     have hv: V ≤ ZTheta V:= le_add_of_nonneg_left zero_le_one; intro j; fin_cases j; rotate_left; · exact (he 0).raise hv (Nat.zero_le _)
     · exact (he 1).raise hv (by change 1 ≤ 0+2; decide)
     apply (Take.zero (ZTheta V)).congr; intro i; filter_upwards with n; funext x v; change 0= fderiv ℝ (jet _ _) v (functorE x e u); rw [show jet (Rh (A i) (n:=n)) 0=fun _=> Rh (A i) 0 from funext fun j=> jet_zero .., fderiv_const_apply];rfl -- implicit
local notation "∆" p:arg => sett _ _ p
-- pair kernels.Catalog startup.* counts richness. r/v positive
variable [Fintype I]
lemma sponsorCake (a:I→RootEdge)(F: Libra.Keys G I→G.Color)(H:ContDiffAt ℝ ω F 0)
    (h:0 ≤ V){p:Clip}(ht:∀ i,(A i).clip=p)(r:ℕ):
    Shut (ZTheta V) (fun i n x=>Cake (sett n x e) b (Dune (A i)) (Rh (A i)) (F ∘ dip a n x) r) (r+1) m:=by
       let Z(s:G.ColorIndex):= ((Phone G).coord s) ∘ F; have hZ(s:G.ColorIndex): ContDiffAt ℝ ω (Z s) 0:= (((Phone G).coord s).toContinuousLinearMap.contDiff.contDiffAt.comp _ H)
       let M0(i:M)(n:Side)(x:Site n):= Pawn.mold (Dune (A i) (n:=n)) 2
       let M1(i:M)(n:Side)(x:Site n):= Pawn.mold (Rh (A i) (n:=n)) 0
       let v(j)(i:M)(n:Side)(x:Site n):= Pawn.mold (Z j∘ dip a n x) r
       let P(s:G.ColorIndex)(j:M)(n:Side)(x:Site n):= LoopM (sett n x e) ((Phone G) s) b (M0 j n x) (M1 j n x) (v s j n x)
       let U:=ZTheta V; rw[show (fun i n x=>Cake (sett n x e) b (Dune (A i)) (Rh (A i)) (F∘ dip a n x) r)=∑ j,P j from funext fun i=>funext fun n=>funext fun x=>(by unfold Cake;rw[Finset.sum_apply,Finset.sum_apply,Finset.sum_apply];rfl)]
       apply Shut.sum; intro j _
       have hu:1 ≤ U:= le_add_of_nonneg_right h; have he:Shut 1 (v j) r m:=by intro i; fin_cases i<;> first|exact monaJet _ a (hZ j) r m|exact monaJet _ a (hZ j) (r+1) m|exact monaJet _ a (hZ j) (r+2) m
       have hf(s:G.ColorIndex): Shut U (fun i n x=>Pry (functorE x e s) (M0 i n x+M1 i n x)) 1 m:=by
            let p(i:M)(n:Side)(x:Site n):= Pry (functorE x e s) (M0 i n x); let q(i:M)(n:Side)(x:Site n):= Pry (functorE x e s) (M1 i n x); rw [show (fun i n x=>Pry (functorE x e s) (M0 i n x+M1 i n x))= p+q from funext fun i=>funext fun n=>funext fun x=>pryAdd _ _ _ (tallJ _ _) (tallJ _ _)]
            exact Shut.add ((readyK e A s ht).taller hu le_rfl) ((readyY e A s h).taller le_rfl (Nat.zero_le _)) 
       let f(i:M)(n:Side)(x:Site n):= Topper (sett n x e) ((Phone G) j) b (M0 i n x+M1 i n x); let g(i:M)(n:Side)(x:Site n):= Topper (sett n x e) ((Phone G) j) b (v j i n x); have hp:Shut U f 1 m:= Tow _ _ _ hf; have hk(s:G.ColorIndex): Shut 1 (fun i n x=> Pry (functorE x e s) (v j i n x)) r m:=by
            intro i; fin_cases i<;> first| exact TakesY e s _ (Z j) (hZ _) r| exact TakesY e s _ (Z j) (hZ _) (r+1)| exact TakesY e s _ (Z j) (hZ _) (r+2)
       have hx:Shut 1 g r m:= Tow _ _ _ hk; apply Shut.sub (A:=f * v j) (B:=g); rotate_left; · exact hx.taller hu (Nat.le_succ r)
       change Shut U _ _ _; rw [← mul_one U,Nat.add_comm]; exact Shut.prod hp he
end YM.OPE.Variance
