import YM.Integration.WilsonIndependentPostedInjection
import YM.Integration.WilsonIndependentSpoutUnshiftedPost

/-! The actual unshifted Schur inlet is the purchased two-part tensor, on the same four-dimensional torus. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedBoard
open Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Halo
open RegulatorIR.Ledger RegulatorIR.Calibration WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentPostedInjection (channel)
open WilsonIndependentPrimitiveCoordinates (printed jo)
open scoped BigOperators Classical Topology

theorem carried {A B D F:Type}(a:A≃D)(b:B≃F)(s:A↪B)(t:D↪F)
    (comm:∀i,b (s i)=t (a i)){r:ℕ}(T:Packet A r)(q:Tuple B r):
    offer t (fun z=>T (a.symm∘z)) (b∘q)=offer s T q:=by
  classical
  by_cases h:q∈Set.range (acrossT s)
  · obtain ⟨x,rfl⟩:=h
    have eq:b∘acrossT s x=acrossT t (a∘x):=funext fun i=>comm (x i)
    rw [eq,offer_eq,offer_eq]
    exact congr_arg T (funext fun i=>a.symm_apply_apply (x i))
  have dead:b∘q∉Set.range (acrossT t):=by
    rintro ⟨u,hu⟩
    apply h
    refine ⟨a.symm∘u,funext fun i=>b.injective ?_⟩
    change b (s (a.symm (u i)))=b (q i)
    rw [comm,a.apply_symm_apply]
    exact congrFun hu i
  rw [offer_zero _ dead,offer_zero _ h]

variable {G:Gauge}
theorem axes (P:Patch)(n:Side)(x:WilsonIndependentSpoutFiniteStencil.Raw G (n*P.L)⊕
    WilsonIndependentSpoutFiniteStencil.Raw G n):
    weaveH (ratioN P.L n) G (WilsonIndependentSpoutUnshiftedPost.coordinates P n x)=jo G P n x:=by
  cases x<;>rfl

variable {W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
    (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)

def posted (n:Side)(e:ℕ):Gen ℝ (Co n (Hinge G (C.pactP f).L)):=
  if e=0 then 0 else WilsonIndependentPostedGrant.finite C Z D f A Ñ N m α n e

def port (e:ℕ):Gen ℝ (Cloth (Hinge G (C.pactP f).L)):=
  if e=0 then 0 else WilsonIndependentPostedGrant.cover C Y Z D f A Ñ N m α e

theorem original (n:Side)(e r:ℕ)(q:Fin r→Joint G (n*(C.pactP f).L) n):
    let P:=C.pactP f
    posted C Z D f A Ñ N m α n e r (weaveH (ratioN P.L n) G∘q)=
      WilsonIndependentSpoutUnshiftedPost.bank P n (C.bore G Z (sheet D) f) α ((story A Ñ N m).1 (n*P.L)) e r q:=by
  intro P
  by_cases gz:e=0
  · simp only [posted,WilsonIndependentSpoutUnshiftedPost.bank,if_pos gz,Pi.zero_apply]
  simp only [posted,WilsonIndependentSpoutUnshiftedPost.bank,if_neg gz,WilsonIndependentPostedGrant.finite,Pi.add_apply]
  apply congrArg₂ (·+·)
  · rw [WilsonIndependentPostedGrant.oldFinite,WilsonIndependentPostedInjection.finite]
    let a:=weaveFine (ratioN P.L n) G
    let b:=weaveH (ratioN P.L n) G
    let s:Woods G (n*P.L)↪Joint G (n*P.L) n:=Embedding.inl
    let t:=channel (Site n) (Larvae G P.L) (Hooks G)
    change offer t (fun z=>WilsonIndependentSpoutReportedQuiet.finite A Ñ N m α e r (n*P.L) (a.symm∘z)) (b∘q)=_
    rw [WilsonIndependentSpoutReportedQuiet.finite,if_neg gz]
    exact carried a b s t (fun _=>rfl) _ q
  · unfold printed WilsonIndependentSpoutUnshiftedPost.stamp
    apply congr_arg (WilsonIndependentSpoutOrdinaryPrimitives.board P n (C.bore G Z (sheet D) f) e r)
    funext i
    apply (jo G P n).injective
    change jo G P n ((jo G P n).symm (weaveH (ratioN P.L n) G (q i)))=
      jo G P n ((WilsonIndependentSpoutUnshiftedPost.coordinates P n).symm (q i))
    rw [Equiv.apply_symm_apply,←axes,Equiv.apply_symm_apply]

theorem earned (simple:G.Simple)(ratio:LocalRatio Ñ)(age:m≤N)(e r:ℕ)(hr:0<r):
    Yields (fun n=>posted C Z D f A Ñ N m α n e r) (port C Y Z D f A Ñ N m α e r):=by
  unfold posted port
  split
  · exact Yields.zero
  exact WilsonIndependentPostedGrant.original C Y Z D f A Ñ simple ratio N m age α e r ⟨0,hr⟩

theorem pure (simple:G.Simple)(ratio:LocalRatio Ñ)(age:m≤N)(n:Side)(e:ℕ):
    Pure (posted C Z D f A Ñ N m α n e):=by
  unfold posted
  split
  · exact fun _=>Smooth.zero
  exact WilsonIndependentPostedGrant.pure C Z D f A Ñ simple ratio N m age α n e

end YM.Integration.WilsonIndependentPostedBoard
