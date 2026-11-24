import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
variable [Fintype I]
local notation "Yp"=>Libra.Keys G I
noncomputable abbrev grain (c:ℝ)(N B:ℕ):ℕ→ℝ
       | 0=>c
       | k+1=> (N:ℝ)* ((1+ (1:ℝ)) *((k:ℝ)+1)* B * grain c N B k)
variable (Q:Tensor.T (Libra.Keys G I) ℝ k)(m B:ℕ)(T:I→RootEdge) {c:ℝ}
local notation "Nk"=>I×G.ColorIndex
omit [Fintype I] in
lemma bread1 (e:RootEdge)(u:G.ColorIndex)(m:ℕ): figure m (fun _ : Fin 1=> (e.1,e.2,u))=(((1+size e.1):ℕ)^m:ℕ):=by
         unfold figure poise; change (↑(stamp _) : ℝ)^m=_; rw [Nat.cast_pow,Page.perimeter]; simp
omit [Fintype I] in
lemma kglee (u :G.ColorIndex):‖Phone G u‖=1:= (show ‖Awake u‖=1 from OrthonormalBasis.norm_eq_one _ _)
lemma paw (i:Nk): ‖PickL G i‖ ≤ 1:=by unfold PickL An; rw [Pi.norm_single,kglee]
lemma monaC (hx:∀ i,(1+ size (T i).1)^m ≤ B)(hp: ∀ x:Fin k→Libra.Keys G I,(∀ i:Fin k,‖x i‖ ≤ 1)→ ‖Q x‖≤ c): UnitL (grain c (Fintype.card (I×G.ColorIndex)) B k) (fun n x y=> Tensor.diagonal Q (dip T n x y)) k m:=by
        induction k with
        | zero=>
            let z:Page (Shade G) 0:=Fin.elim0; let p:=Q (fun _=>0); have hv:soot m (Pi.single z p) c:=by
                   apply (Sack.lineOne z (figure m) (le_trans zero_le_one (payer m)) p).tips
                   have hh: ‖p‖ ≤ c := hp _ (fun i=>Fin.elim0 i); rw [show figure m z=1 from ?_,one_mul]; exact hh
                   unfold figure poise; change (↑(stamp z):ℝ)^m=1; rw [Page.perimeter z]; simp
            apply (UnitL.kilo _ hv).congrZ; filter_upwards with n; funext b v; unfold Flume.Script.value scribe; rw [tsum_eq_single z,Pi.single_eq_same]; simp only [render,Fintype.prod_empty,mul_one]; exact congr_arg Q (Subsingleton.elim ..); exact fun i hi=>False.elim (hi (Subsingleton.elim ..))
        | succ k ih =>
            let V(i):= Q.curryLeft (PickL G i); let p(i:I×G.ColorIndex)(n:Side)(x:Site n)(y:Bid.Dir G n):= keyMark n x (T i.1) i.2 y * Tensor.diagonal (V i) (dip T n x y); let f(i:I×G.ColorIndex):ℝ:= (1+(1:ℝ)) *((k:ℝ)+1)* B*grain c (Fintype.card (I×G.ColorIndex)) B k
            have hv(i):UnitL (f i) (p i) (k+1) m:=by
                 have hb:= bread (T i.1) i.2 m; let j(n:Side)(x:Site n)(y:Bid.Dir G n):= keyMark n x (T i.1) i.2 y
                 have hj: UnitL (B:ℝ) j 1 m:= (UnitL.kilo (punch (T i.1) i.2) (hb.tips (le_trans (le_of_eq (bread1 ..)) (by exact_mod_cast hx i.1)))).congrZ (Eventually.of_forall fun n=>funext fun x=>funext fun y=> poster ..)
                 have hh:= ih (V i) (fun x hx=>hp (Fin.cons (PickL G i) x) (fun j=>by refine Fin.cases ?_ ?_ j;simpa only[Fin.cons_zero] using! paw i; exact fun i=>by simpa only [Fin.cons_succ] using hx i)); rw [show k+1=1+k from Nat.add_comm ..]; convert hj.product hh using 1; simp [f]; rfl
            apply (UnitL.sumZ f p univ (fun i _=>hv i)).taller ?_ le_rfl|>.congrZ
            · filter_upwards with n; funext x y; let t:=dip T n x y; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rw [show Tensor.diagonal Q _= Q.curryLeft t (fun _=>t) from congr_arg Q (by ext j; refine Fin.cases ?_ (fun i=>?_) j<;>rfl)]; nth_rw 1 [resident t];rw [map_sum,_root_.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,_root_.smul_apply]; rfl -- occurrence
            unfold grain f; rw [Finset.sum_const,card_univ,nsmul_eq_mul]
end YM.OPE.Variance
