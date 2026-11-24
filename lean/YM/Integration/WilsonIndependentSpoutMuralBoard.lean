import YM.Integration.WilsonIndependentSpoutMuralWindow
import YM.Integration.WilsonIndependentSpoutPrimitiveReport

/-! The original signed Wilson top on the physical ordinary boards and its
actual cover input. Every plaquette and each angular rank are retained. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMuralBoard
open Filter Function Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open RegulatorIR RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Prim
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Ward Bank
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open WilsonIndependentSpoutPrimitiveReport (axis picture)
open WilsonIndependentSpoutMuralWindow (fronts)
open WilsonIndependentSpoutOrdinaryPlate (base sample)
open scoped Classical BigOperators Topology
variable {G:Gauge}{I:Type}{M:I→ℕ}(t:Page M→Scale)(w:I)

def board (n:Side):Orders (Raw G n):=fun e r=>
  ∑p:Face (Per n),Stalk.collect (fun z:Tuple (Foot G) r=>coordinates n∘z) (Circuit.mural G t w (base p) e r)

private def project (n:Side)(p:Face ℤ):Face (Per n):=(wrap n p.1,p.2)

private theorem back {n:Side}(p:Face (Per n)):project n (base p)=p:=Prod.ext (wrap_lift _) rfl

theorem original (e r:ℕ)(x:Tuple (Foot G) r):
    ∀ᶠ n:Side in atTop,board t w n e r (coordinates n∘x)=Circuit.padV G t w e r x:=by
  classical
  let T:=Circuit.mural G t w
  have zero (b:Face ℤ):T b e 0=0:=WilsonIndependentSpoutMuralWindow.scalar t w b e
  rcases Nat.eq_zero_or_pos r with h|hr
  · subst r
    filter_upwards [] with n
    unfold board Circuit.padV many massive
    simp only [zero,Stalk.collect,Pi.zero_apply,tsum_zero,Finset.sum_const_zero,Finset.sum_apply,T]
  let pin:Fin r:=⟨0,hr⟩
  let a:=fronts (x pin)
  have present (p:Face ℤ):∀ᶠ n:Side in atTop,base (project n p)=p:=by
    filter_upwards [lift_ready p.1] with n h
    exact Prod.ext h rfl
  filter_upwards [eventually_all.mpr (fun j=>WilsonIndependentSpoutMuralWindow.originated (x j)),
    (eventually_all_finset a).mpr (fun p _=>present p)] with n lawful can
  have single (p:Face (Per n)):
      Stalk.collect (fun z:Tuple (Foot G) r=>coordinates n∘z) (T (base p) e r) (coordinates n∘x)=T (base p) e r x:=by
    apply tsum_eq_single (⟨x,rfl⟩:Stalk (fun z:Tuple (Foot G) r=>coordinates n∘z) (coordinates n∘x))
    intro z hz;by_contra nz
    apply hz
    apply Subtype.ext;funext j
    apply lawful j p _ _ (congr_fun z.property j)
    by_contra miss
    exact nz (WilsonIndependentSpoutMuralWindow.selected t w (base p) e r z.val j miss)
  have sub:a⊆(Finset.univ:Finset (Face (Per n))).image base:=fun b hb=>
    Finset.mem_image.mpr ⟨project n b,Finset.mem_univ _,can b hb⟩
  have outside (b:Face ℤ)(miss:b∉a):T b e r x=0:=by
    apply WilsonIndependentSpoutMuralWindow.selected t w b e r x pin
    exact fun f=>miss (WilsonIndependentSpoutMuralWindow.front f)
  change (board t w n e r) _=∑'b,T b e r x
  rw [tsum_eq_sum (s:=a) outside]
  calc _=∑p:Face (Per n),T (base p) e r x:=by
         unfold board;rw [Finset.sum_apply];exact Finset.sum_congr rfl (fun b _=>single b)
       _=∑p∈(Finset.univ:Finset (Face (Per n))).image base,T p e r x:=by
         rw [Finset.sum_image (fun _ _ _ _ h=>(show LeftInverse (project n) base from back).injective h)]
       _=_:=(Finset.sum_subset sub (fun b _ h=>outside b h)).symm

theorem reading (n:Side)(e cap:ℕ)(y:TreeVars G n):
    drums (board t w n e) cap (axis y)=∑p:Face (Per n),drums (Circuit.mural G t w (base p) e) cap (sample y):=by
  unfold drums
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro r _
  change strum (∑b:Face (Per n),Stalk.collect (fun z:Tuple (Foot G) r=>coordinates n∘z) (Circuit.mural G t w (base b) e r)) (axis y)=_
  unfold strum
  rw [tsum_fintype]
  simp only [Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro b _
  change (∑z,Stalk.collect (fun q:Tuple (Foot G) r=>coordinates n∘q) (Circuit.mural G t w (base b) e r) z*noodle (axis y) z)=
    strum (Circuit.mural G t w (base b) e r) ((axis y)∘coordinates n)
  rw [←picture (coordinates n) _ ((Circuit.serene G t w (base b)).sized e r) (axis y)]
  exact (tsum_fintype _).symm

theorem finite (bare:t (Page.opening M w)=Clocks.flat)(n:Side)(e:ℕ)(he:0<e)(y:TreeVars G n):
    drums (board t w n e) (e+2) (axis y) = -MvPolynomial.eval y (totalR (topW G n e)):=by
  rw [reading,WilsonIndependentSpoutOrdinaryTop.original t w bare y e he]

end YM.Integration.WilsonIndependentSpoutMuralBoard
