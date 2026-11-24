import YM.Integration.WilsonIndependentSpoutFiniteStencil

/-! Angular coefficients of the genuine finite ordinary sum of the actual
issued primitive tensors stabilize to its selected infinite cover bank. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives
open Filter Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Prim
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration Tree
open WilsonIndependentSpoutPrimitiveWindow WilsonIndependentSpoutPrimitiveFronts
open WilsonIndependentSpoutFiniteStencil (Keys Raw fold)
open scoped Classical BigOperators Topology

abbrev liftKey {P:Patch}{n:Side}:Keys P n→Branchix:=WilsonIndependentSpoutFiniteStencil.original
def project (P:Patch)(n:Side):Branchix→Keys P n:=Sum.map (around (n*P.L)) (around n)

theorem back {P:Patch}{n:Side}(v:Keys P n):project P n (liftKey v)=v:=by
  cases v <;> simp [project,liftKey,WilsonIndependentSpoutFiniteStencil.original,WilsonIndependentSpoutOrdinarySpring.home]

theorem injective (P:Patch)(n:Side):Injective (liftKey:Keys P n→Branchix):=
  (show LeftInverse (project P n) (liftKey:Keys P n→Branchix) from back).injective

theorem opening (P:Patch)(y:Branchix):
    ∀ᶠ n:Side in atTop,liftKey (project P n y)=y:=by
  cases y with
  | inl y=>
    filter_upwards [(multi_end P.L).eventually (lift_ready y.1)] with n hn
    exact congr_arg Sum.inl (Prod.ext hn rfl)
  | inr y=>
    filter_upwards [lift_ready y.1] with n hn
    exact congr_arg Sum.inr (Prod.ext hn rfl)

def board {G:Gauge}(P:Patch)(n:Side)(T:Branchix→Orders (KFoot G)):
    Orders (Raw G (n*P.L)⊕Raw G n):=fun e r=>
  ∑u:Keys P n,Stalk.collect (fun x:Tuple (KFoot G) r=>fold P n ∘x) (T (liftKey u) e r)

variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)

theorem original (e r:ℕ)(x:Tuple (KFoot G) r)(pin:Fin r):
    let P:=C.pactP f;let T:=C.bore G Z (sheet D) f
    ∀ᶠ n:Side in atTop,board P n T e r (fold P n∘x)=((C.dialect Y G Z (sheet D)).frames f).addon e r x:=by
  intro P T
  let ω:=fronts P (x pin)
  have clean:∀ᶠ n:Side in atTop,∀j:Fin r,∀(b:Keys P n)(u:KFoot G),u∈sites G P (liftKey b)→
      fold P n u=fold P n (x j)→u=x j:=
    eventually_all.mpr fun j=>WilsonIndependentSpoutFiniteStencil.genuine P (x j)
  filter_upwards [clean,(eventually_all_finset ω).mpr (fun b _=>opening P b)] with n trusted done
  have rolled (b:Keys P n):
      Stalk.collect (fun z:Tuple (KFoot G) r=>fold P n∘z) (T (liftKey b) e r) (fold P n∘x)=
      T (liftKey b) e r x:=by
    change (∑'w:Stalk (fun z:Tuple (KFoot G) r=>fold P n ∘z) (fold P n∘x),T (liftKey b) e r w.val)=_
    rw [tsum_eq_single (⟨x,rfl⟩:Stalk (fun z:Tuple (KFoot G) r=>fold P n∘z) (fold P n∘x))]
    intro w hw
    by_contra nz
    apply hw
    apply Subtype.ext
    funext j
    apply trusted j b _ _ (congr_fun w.property j)
    by_contra miss
    exact nz (selected C Z D f (liftKey b) e r w.val j miss)
  have cover:ω⊆(Finset.univ:Finset (Keys P n)).image liftKey:=by
    intro b hb
    exact Finset.mem_image.mpr ⟨project P n b,Finset.mem_univ _,done b hb⟩
  rw [WilsonIndependentSpoutPrimitiveFronts.original C Y Z D f e r x pin]
  calc board P n T e r (fold P n∘x) = ∑b:Keys P n,T (liftKey b) e r x:=by
         unfold board;rw [Finset.sum_apply]
         exact Finset.sum_congr rfl (fun b _=>rolled b)
       _ = ∑b∈(Finset.univ:Finset (Keys P n)).image liftKey,T b e r x:=by
         rw [Finset.sum_image (fun _ _ _ _ h=>(injective P n) h)]
       _ = ∑b∈ω,T b e r x:=by
         apply (Finset.sum_subset cover ?_).symm
         intro b _ miss
         apply selected C Z D f b e r x pin
         intro inside
         exact miss ((finite P (x pin)).mem_toFinset.mpr inside)

end YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives
