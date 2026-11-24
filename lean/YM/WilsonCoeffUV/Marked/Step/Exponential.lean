import YM.WilsonCoeffUV.Marked.Step.SatHeat
/-!
# Era logs and exponential

Unique exact coefficient families, NOT anchored root sums/lazy aggregation
(hidden pair origins NOT interchangeable). Each entry computed all powers
(native Level unbounded order). Distinct mark arity.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix
open Work.F08 Precision AnalyticNext.QuarticMatch.Sheets Wilson MultiNext.SignedSource Tree
open scoped Topology BigOperators
variable {n:Side}{ι:Type}{J K S T:Finset ι}{D k:ι→ℕ}{k' i j e r h N m l:ℕ}{G:Gauge}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
lemma unstamped : Auth k' (0:Era G V):=by
    have h: ∀ i∈ (∅:Finset Unit), Auth k' ((fun _ : Unit=> (0:Era G V)) i):=by simp
    simpa using Auth.sum h
-- unit transported as unit
private abbrev vTim (w:V): ℝ →L[ℝ] V:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w
def pieceO (G:Gauge): Era G ℝ:= (fun _=>uband 1,uband 1)
lemma piece_auth : Auth j (pieceO G):= by
    refine ⟨fun i t=>?_, fun n=>uband_length _ _ j, fun n=>uband_cost _ _, fun n=>?_⟩
    · cases t with
      | succ t=> unfold pieceO; simp_rw [uband,shine_dark (by omega : 0≠ t+1)]; exact Bends.zero
      | zero=> refine ⟨fun x=>tendsto_const_nhds, 1,‖(pieceO G).2 i 0 (fun x=>x.elim0)‖,one_pos, Eventually.of_forall fun n=>⟨norm_nonneg _,fun x=>?_⟩⟩
               simp only [pieceO,uband,shine_lit]; simp [tread,league, tor]
    apply certify (k:=0) (ι:=Unit) (fun _=>LinearMap.id) (fun x y z=> z ()) _ (uband_length (Woods G n) 1 0); intro x
    rw [show ply LinearMap.id (uband (U:=Woods G n) 1)=uband 1 from rfl,uband_flash,map_one]; intro Z I x V L h; rw [map_one,map_one]
abbrev family (G:Gauge)(D:ι →ℕ):= (S:Finset ι)→ Era G (Pen D S)
def readO {S} (A:Case D)(X:Era G (Pen D S))(n:Side):= flash (pPly A S (X.1 n))

def mass (k:ι→ℕ)(J:Finset ι):ℕ:= ∑ i∈ J,k i
def Eu (k:ι→ℕ)(M:family G D):Prop:= ∀ S,Auth (mass k S) (M S)

def puff (D:ι→ℕ)(G:Gauge): Era G (Pen D ∅) := tuftV (vTim (ochre D)) (pieceO G)
lemma paidO (D:ι→ℕ): Auth j (puff D G):= Auth.tuft piece_auth _
lemma pen_puff (D:ι→ℕ)(G:Gauge)(A:Case D)(n:Side) : pPly A ∅ ((puff D G).1 n)= uband 1:=by ext1 i; funext j x; change touch A ∅ (uband 1 i j x • ochre D)=_; rw [map_smul,ochre_v]; exact mul_one _
lemma readingO (A:Case D): readO A (puff D G) n=1:=by simp [readO,pen_puff,uband_flash]
lemma read_emp {S} (A:Case D)(G:Gauge)(n:Side): readO A (0:Era G (Pen D S)) n=0:=by unfold readO; change flash (pPly _ _ 0)=_; rw [map_zero]; ext1 i; simp [flash,totalR]
lemma read_lot (A:Case D)(n:Side)(P Q:Era G (Pen D S))(p:Auth j P)(q:Auth j Q): readO A (P-Q) n= readO A P n-readO A Q n:=by unfold readO; simp only [Prod.fst_sub,Pi.sub_apply,map_sub]; exact flash_sub (finite_shell (ply_shell _ (p.span _))) (finite_shell (ply_shell _ (q.span _)))
lemma read_rho (A:Case D)(n:Side)(P:Era G (Pen D S))(p:Auth j P)(c:ℝ): readO A (c • P) n= c • readO A P n:=by unfold readO; simp only [Prod.smul_fst,Pi.smul_apply,map_smul]; exact flash_mu _ (ply_shell _ (p.span _))
lemma read_Sum {t: Type}{P:t→Era G (Pen D S)} {X:Finset t}(A:Case D)(n:Side)(p:∀ i∈X,Auth j (P i)): readO A (∑ i∈X,P i) n=∑ i∈X,readO A (P i) n:=by unfold readO; rw [Prod.fst_sum,Finset.sum_apply,map_sum]; exact flash_term _ fun i hi=> ply_shell _ ((p i hi).span _)
lemma read_ext (P Q:Era G (Pen D S))(p:Auth j P)(q:Auth i Q)(h:∀ A n,readO A P n=readO A Q n): P=Q:= Auth.ext p q (funext fun n=> by
    funext i j x; apply pen_inj; intro A
    have hp:=by_flash (ply_shell ((touch A S).toLinearMap) (p.span n)) (ply_shell _ (q.span n)) (fun i=> ply_pure _ (p.pale n i)) (fun i=> ply_pure _ (q.pale n i)) (h A n)
    exact congr_fun (congr_fun (congr_fun hp i) j) x)
lemma puff_verse (A:Levels G){Ñ:ChartRatio G}(p:m<N)(g:G.Simple)(f:LocalRatio Ñ)(D:ι→ℕ): verseI A Ñ m N k' (puff D G)=puff D G:=by
    apply read_ext _ _ (Auth.verse A p g f (paidO D)) (paidO (j:=0) D); intro V n
    rw [readingO]; unfold readO
    let L:=ll A m; let K:=A.clock.kernel; let X:= ratioHigh A Ñ N m; let T:=(puff D G).1 (n*L.L); let Y:=reed (R:=ℝ) (stepAt L K n) (xree L K n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 _) k'
    let u:=reed (stepAt L K n) (xree L K n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 _) k' T
    have he: ply (touch V ∅).toLinearMap u= Y (ply (touch V ∅).toLinearMap T):= reed_maps _ _ _ _ k' (touch V ∅).toLinearMap
    change flash (ply (touch V ∅).toLinearMap (Blue.mix X u))=_; rw [ply_mixX,he, show ply (touch V ∅).toLinearMap T=uband 1 from pen_puff D G V _,show Y (uband 1)=uband 1 from rumble .., reset_zinc]
    rw [show reel X 1=1 from map_one _, uband_flash,map_one]

variable [DecidableEq ι]
def waxV (h:J⊆ S)(X:Era G (Pen D J))(Y: Era G (Pen D (S\J))) : Era G (Pen D S):= (fun n=> foam h (X.1 n) (Y.1 n),foam h X.2 Y.2)
lemma read_wax (h:J⊆S)(A:Case D)(n:Side)(P:Era G (Pen D J))(Q:Era G (Pen D (S\J)))(p:Auth i P)(q:Auth j Q): readO A (waxV h P Q) n= readO A P n * readO A Q n:=by
    unfold readO waxV; dsimp only; rw [fp]; exact woadap _ _ (finite_shell (ply_shell _ (p.span _))) (finite_shell (ply_shell _ (q.span _)))
lemma paidW (h:J⊆ S)(X:Era G (Pen D J))(Y: Era G (Pen D (S\J)))(p:Auth i X)(q:Auth j Y): Auth (i+j) (waxV h X Y):=by
   let W:=waxV h X Y; have hv n : shellK (i+j) (W.1 n):= foam_shell h _ _ (p.span n) (q.span n); refine ⟨crest_foam h p.wing q.wing,hv,fun n i=> foam_pure h _ _ i,fun n=>certify (fun i : Case D=> (touch i S).toLinearMap) (fun _ _ hp=>pen_inj _ _ hp) _ (hv n) (fun A=>?_)⟩; change rollTest (readO A (waxV ..) n) (readO A (waxV ..) n) 1 0; intro Z I x V L z
   rw [read_wax _ A n X Y p q,map_mul,map_mul]; exact congr_arg₂ (·*·) (p.token n (touch A _).toLinearMap z) (q.token n (touch A _).toLinearMap z)
end YM.WilsonCoeffUV.Wheel.Mark
