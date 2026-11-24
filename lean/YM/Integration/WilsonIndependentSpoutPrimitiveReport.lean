import YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives
import YM.Integration.WilsonIndependentSpoutPaidAddon

/-! Evaluate the actual ordinary primitive coefficient table on its complete
joint field. The same table converges coefficientwise to the genuine addon. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPrimitiveReport
open Filter Function Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Geometry.Field RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Calibration RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Ward
open Tree FreeResolvent Metric Precision Exterior WilsonIndependentPublicFreeTrain
open WilsonIndependentSpoutOrdinaryPrimitives
open WilsonIndependentSpoutFiniteStencil (Keys Raw fold)
open WilsonIndependentSpoutOrdinaryPlate WilsonIndependentSpoutOrdinarySpring
open scoped Classical BigOperators Topology Matrix

theorem picture {I J:Type}(F:I→J){r:ℕ}(T:Packet I r)(paid:Bounded T)(w:J→ℝ):
    strum (Stalk.collect (fun z:Tuple I r=>F∘z) T) w=strum T (w∘F):=by
  let U (z:Tuple I r):=T z*noodle (w∘F) z
  have hs:Summable U:=summable_of_hasFiniteSupport (Set.Finite.subset paid (by
    intro z h
    contrapose! h
    change ¬U z≠0
    simp only [not_not]
    unfold U;rw [Function.notMem_support.mp h,zero_mul]))
  unfold strum
  change _=∑'z,U z
  rw [←Stalk.collected_sum (fun z:Tuple I r=>F∘z) hs]
  apply tsum_congr;intro z
  unfold Stalk.collect
  rw [←tsum_mul_right]
  apply tsum_congr;intro y
  unfold U
  change _=T y.val*noodle w (F∘ y.val)
  rw [(show F∘y.val=z from y.property)]

variable {G:Gauge}
theorem reading (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))
    (paid:∀b e r,Bounded (T b e r))(e cap:ℕ)(w:Raw G (n*P.L)⊕Raw G n→ℝ):
    drums (board P n T e) cap w=∑b:Keys P n,drums (T (liftKey b) e) cap (w∘fold P n):=by
  unfold drums
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro r _
  change strum (∑b:Keys P n,Stalk.collect (fun z:Tuple (KFoot G) r=>fold P n∘z) (T (liftKey b) e r)) w=_
  unfold strum
  rw [tsum_fintype]
  simp only [Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro b _
  change (∑z,Stalk.collect (fun q:Tuple (KFoot G) r=>fold P n∘q) (T (liftKey b) e r) z*noodle w z)=strum (T (liftKey b) e r) (w∘fold P n)
  rw [←picture (fold P n) _ (paid (liftKey b) e r) w]
  exact (tsum_fintype _).symm

def axis {n:Side}(y:TreeVars G n)(z:Raw G n):ℝ:=((cloth G n).symm y (z.1.1,coord z.1.2)) z.2

theorem fields (P:Patch){n:Side}(a:TreeVars G (n*P.L))(b:TreeVars G n):
    (Sum.elim (axis a) (axis b))∘fold P n=joined a b:=by
  funext x;cases x <;>rfl

private theorem resized {c:Side}{Q P:Patch}(same:Q=P)(T:Branchix→Orders (KFoot G))(e:ℕ)
    (u:TreeVars G (c*Q.L))(b:TreeVars G c):
    let u':TreeVars G (c*P.L):=(congr_arg (fun L:Patch=>TreeVars G (c*L.L)) same) ▸ u
    (∑j:Edge (Site (c*Q.L)),drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg j)) e) e (joined u b))+
      (∑j:Edge (Site c),drums (T (.inr (WilsonIndependentSpoutOrdinarySpring.peg j)) e) (e+2) (joined u b))=
    (∑j:Edge (Site (c*P.L)),drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg j)) e) e (joined u' b))+
      (∑j:Edge (Site c),drums (T (.inr (WilsonIndependentSpoutOrdinarySpring.peg j)) e) (e+2) (joined u' b)):=by
  subst P;rfl

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(s:ℕ)(inc:Matches A C K s f.volW)

include Y in
theorem original (c:Side)(e:ℕ)(he:0<e):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=C.pactP f
    let S:=mStep A c m;let F:=repeatF S;let Q:=roam A N m c
    let H:=freeForms A N (m+1);let H':=freeForms A N m
    let α:=tale (D f.prev).dine;let Ñ:=XSpace.Bare.chart G
    let T:=C.bore G Z (sheet D) f;let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
    ∀x:Lawn (Active G F⊕Woods G c),
      let z:=overM G S F *ᵥ x;let u:=camber G (extractV G S F Q) *ᵥ z;let b:=rightArm z
      let u':TreeVars G (c*P.L):=(congr_arg (fun L:Patch=>TreeVars G (c*L.L)) (inc.patches f rfl)) ▸ u
      MvPolynomial.eval x (coeff e (WilsonIndependentSpoutSchurFrame.field S F H H' Q α Ñ V))=
        MvPolynomial.eval u (coeff e (orbC (precisionC G _ H)-flash (mix α V)))+
        drums (board P c T e) (e+2) (Sum.elim (axis u') (axis b)):=by
  intro N m P S F Q H H' α Ñ T V x z u b u'
  have h:= (WilsonIndependentSpoutPaidAddon.original C Z D f Y A s inc c e he).2 x
  have closeP:S.patch=P:=inc.patches f rfl
  have human:∀v i j,Bounded (T v i j):=fun v i j=>(C.wheeled G Z (sheet D) f v).sized i j
  rw [reading P c T human,fields,Fintype.sum_sum_type]
  have clean (p:Edge (Site (c*P.L))):
      drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) (e+2) (joined u' b)=
      drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) e (joined u' b):=by
    unfold drums
    apply (Finset.sum_subset (Finset.range_mono (by omega)) ?_).symm
    intro r _ hr
    simp only [Finset.mem_range,not_lt] at hr
    rw [show T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e r=0 from by
          by_contra hn
          have w: r≤e+0:=(C.wheeled G Z (sheet D) f (.inl (WilsonIndependentSpoutOrdinarySpring.peg p))).scope_ e r hn
          omega,strum_zero]
  simp only [liftKey,WilsonIndependentSpoutFiniteStencil.original,Sum.map_inl,Sum.map_inr,clean]
  apply h.trans
  rw [add_assoc]
  apply congr_arg (fun z:ℝ=>MvPolynomial.eval u (coeff e (orbC (precisionC G _ H)-flash (mix α V)))+z)
  exact resized (Q:=loose A m) (P:=P) closeP T e u b

end YM.Integration.WilsonIndependentSpoutPrimitiveReport
