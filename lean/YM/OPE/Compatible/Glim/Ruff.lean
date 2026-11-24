import YM.OPE.Compatible.Glim.Suns
/-! # Finite stencils. Registered before N but marks may wrap. -/
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
abbrev RootEdge:= Cover × Axis
def placed (n:Side)(x:Site n)(p:RootEdge):edgeV n := (x+wrap n p.1,p.2)
def sett(n:Side)(x:Site n)(e:RootEdge):= whiz (placed n x e)
noncomputable abbrev dip (U:I→RootEdge)(n:Side)(x:Site n): Bid.Dir G n→L[ℝ] Libra.Keys G I:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (sett n x (U i))
noncomputable abbrev keyMark(n:Side)(x:Site n)(e:RootEdge)(u:G.ColorIndex)(p:Bid.Dir G n):= (Phone G).coord u (p (sett n x e))
noncomputable def punch (e:RootEdge)(u:G.ColorIndex):Script (Shade G) 1:= Pi.single (fun _:Fin 1=> (e.1,e.2,u)) 1
lemma bread (e:RootEdge)(u:G.ColorIndex)(m:ℕ): soot m (punch e u) (figure m (fun _:Fin 1=> (e.1,e.2,u))):=by unfold punch; simpa only [norm_one,mul_one] using! (Sack.lineOne (fun _:Fin 1=> (e.1,e.2,u)) (figure m) (le_trans zero_le_one (payer _)) 1)
lemma phone_eq (i:G.ColorIndex)(u:G.Color):(Phone G).coord i u=u i:=by
     unfold Phone; change _=u i; rw [show (Awake (G:=G)).toBasis.coord i u=_ from (show _= (Awake (G:=G)).toBasis.repr u i from rfl),OrthonormalBasis.coe_toBasis_repr_apply];rfl
lemma poster (n:Side)(x:Site n)(q:Bid.Dir G n)(e:RootEdge)(u:G.ColorIndex): Flume.Script.value x (punch e u) (spool G n q)= keyMark n x e u q:=by
    unfold keyMark Flume.Script.value scribe punch; rw [tsum_eq_single (fun _:Fin 1=> (e.1,e.2,u)),Pi.single_eq_same,one_mul]; unfold render; rw[Fintype.prod_unique,phone_eq];rfl; intro b hb; rw[Pi.single_eq_of_ne hb,zero_mul]
lemma Takes₁ (e:RootEdge)(u:G.ColorIndex)(m:ℕ): Take (Z:=Z) 1 (fun _ n x y=>keyMark n x e u y) 1 m:=by
    let U:Z→ Script (Shade G) 1:= fun _=> punch e u; let C:=figure m (fun _ :Fin 1=> (e.1,e.2,u)); have h:= Take.bead (q:=1) (m:=m) U C (zero_le_one.trans (payer _ _)) (fun _=>by rw [Pi.one_apply,mul_one]; exact bread e u m); apply h.congr; intro _; exact Eventually.of_forall fun n=> funext fun x=>funext fun y=> poster ..
lemma Takes0 (G:Gauge)(x:ℝ): Take (Z:=Z) (k:=0) (m:=m) (G:=G) 1 (fun _:_=>fun _ _ _=>x):=by
    let z:Page (Shade G) 0:= Fin.elim0
    let p:Script (Shade G) 0:= Pi.single z x; have ht:=Take.bead (fun _:Z=>p) (figure m z*‖x‖) (q:=1) (mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _)) (m:=m) (fun _=>by rw [Pi.one_apply,mul_one]; exact Sack.lineOne z (figure m) (le_trans zero_le_one (payer _)) x)
    apply Take.congr ht; intro i; filter_upwards with n; funext b v; unfold p Flume.Script.value scribe; rw [tsum_eq_single z,Pi.single_eq_same]; simp [render]; exact fun b hb=>False.elim (hb (Subsingleton.elim ..))
-- scalar linear read from selection
variable [Fintype I]
noncomputable abbrev PickL (G:Gauge)(L:I×G.ColorIndex): Libra.Keys G I:= An L.1 (Phone G) L.2
lemma resident (q:Libra.Keys G I): q=∑ i:I×G.ColorIndex, ((Phone G).coord i.2 (q i.1)) • PickL G i:=by
    funext i; rw [Finset.sum_apply,Fintype.sum_prod_type,sum_eq_single i]; symm; apply Eq.trans _ ((Phone G).sum_repr ..); apply Finset.sum_congr rfl; intro j _; simp only [Pi.smul_apply,PickL,An,Pi.single_eq_same];rfl
    · intro j _ hj; apply Finset.sum_eq_zero; intro k _; simp only[Pi.smul_apply,PickL,An]; rw [Pi.single_eq_of_ne hj.symm,smul_zero]
    simp
lemma mona (T:Tensor.T (Libra.Keys G I) ℝ k)(m:ℕ)(Y:I→RootEdge): Take (Z:=Z) 1 (fun _ n x y=> Tensor.diagonal T (dip Y n x y)) k m:=by
    induction k with
    | zero=> have ht:= Takes0 (Z:=Z) (m:=m) G (Tensor.diagonal T 0); apply ht.congr; exact fun i=> Eventually.of_forall fun v=>funext fun j=>funext fun a=>congr_arg T (Subsingleton.elim ..)
    | succ k ih=>
        let V(i):= T.curryLeft (PickL G i); let p(i:I×G.ColorIndex)(_:Z)(n:Side)(x:Site n)(y:Bid.Dir G n):= keyMark n x (Y i.1) i.2 y * Tensor.diagonal (V i) (dip Y n x y)
        have hv(i):Take 1 (p i) (k+1) m:=by rw [show k+1=1+k from Nat.add_comm ..,← one_mul (1:Z→ℝ)]; exact Take.product (Takes₁ _ _ m) (ih (V i)) -- namespace
        apply (Take.Sum Finset.univ p (fun i _=>hv i)).congr; intro i; filter_upwards with n; funext x y; let t:=dip Y n x y; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rw [show Tensor.diagonal T _= T.curryLeft t (fun _=>t) from congr_arg T (by ext j; refine Fin.cases ?_ (fun i=>?_) j<;>rfl)]; nth_rw 1 [resident t];rw [map_sum,_root_.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,_root_.smul_apply]; rfl -- occurrence
lemma monaJet (F: Libra.Keys G I→ℝ)(Y:I→RootEdge)(h:ContDiffAt ℝ ω F 0)(k m:ℕ): Take (Z:=Z) 1 (fun _ n x=> jet (F ∘ dip Y n x) k) k m:=by
    apply (mona (Tensor.coeff F k 0) m Y).congr; intro i; filter_upwards with n; funext y z; exact (congr_arg JetS.s (congr_fun (moldC (dip Y _ _) F h k) z)).symm
end YM.OPE.Variance
