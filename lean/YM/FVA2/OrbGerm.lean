import YM.FVA2.Index
import YM.PertExtension.Normalized
import YM.FormalOPE.RG10.Inherit.Atelier

/-!
# Arbitrary-chart transfer of the `Orb.PreTest` germ convention

In particular lift to arbitrary layouts/tree stencils with zero and entrywise link derivatives;
no change in source or transform of markers is made.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.OrbGerm
open MeasureTheory Function Set Filter Lattice XSpace PertExtension
open FormalOPE.RG10.Inherit
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Lattice.Side}

/-- Compatibility requirement only on the links. -/
structure AtBase (f:E → G.El) : Prop where
  starts:f 0=1
  smooth: ContDiffAt ℝ ω (G.mat ∘ f) 0
variable {f g:E→G.El}
namespace AtBase
lemma stay : AtBase (G:=G) (fun _:E=>1):= ⟨rfl,contDiffAt_const⟩
lemma mul (h:AtBase f)(hv:AtBase g): AtBase (fun t=> f t*g t):= by
  refine ⟨?_,?_⟩
  · rw [h.starts,hv.starts,mul_one]
  simp only [Function.comp_def, G.mat_mul]; exact h.smooth.mul hv.smooth
lemma inv (h:AtBase f): AtBase (fun t=> (f t)⁻¹):= by
  refine ⟨?_,?_⟩
  · rw [h.starts,inv_one]
  simp only [Function.comp_def,G.mat_inv]; exact (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ h.smooth
lemma exp {f:E→G.Color}(h:ContDiffAt ℝ ω f 0)(he:f 0=0): AtBase (G.lieExp ∘ f):=by
  refine ⟨by simp [he],?_⟩
  rw [←comp_assoc]; exact G.exp_jet.contDiffAt.comp _ h
variable {b:E→Orb.Trees n→G.El}
lemma on_frame (h:∀ i,AtBase (fun x=> b x i))(i:Site n): AtBase (fun x=> Orb.frame (b x) i):=by
  let U(x:E):= Orb.liftLinks (Orb.splitLink (b x) (fun _=>1))
  have he (j):AtBase (G:=G) (fun x:E=> Orb.splitLink (b x) (fun _=>1) j):=by dsimp only [Orb.splitLink]; split; exact h _; exact stay
  have hz (e):AtBase (G:=G) (fun x:E=> U x e):=by
     dsimp only [U,Orb.liftLinks]; split_ifs
     · exact he _
     exact (he _).inv
  have hr (d:Step) y:AtBase (G:=G) (fun x:E=> d.read (U x) y):=by dsimp only [Step.read]; split; exact (hz _).inv; exact hz _
  induction m:Orb.depth i using Nat.strong_induction_on generalizing i with
  | h m ih=>
    conv => arg 1; ext x; rw [Orb.frame.eq_1]
    by_cases H:Orb.vertex i=0
    · simpa only [dif_pos H] using (stay : AtBase (G:=G) (fun _:E=>1))
    simp only [dif_neg H]; refine AtBase.mul (ih _ ?_ _ rfl) ((hr _ _).inv)
    have hG:= Orb.down_spec H; unfold Orb.Falls at hG; exact hG.trans_eq ((Orb.depth_vertex i).trans m)
end AtBase

variable {b:E→Orb.OEdge n→G.El}

lemma adapt (h:Even n.val){O:Wilson.Config G n→ℝ}(ht:Orb.PreTest O)(hp:∀ i,AtBase (fun x=>b x i)):
    ContDiffAt ℝ ∞ (O ∘ Orb.liftLinks ∘ b) 0:=by
 let X x (i:Orb.Trees n):=b x i.val; let Y x(i:Orb.Cotree n):= b x i.val; let Z x:= Orb.fresh (X x) (Y x)
 have hz (i:Orb.Cotree n):AtBase (G:=G) (fun x:E=> Z x i):=by
    let F y:= fun x=> Orb.frame (X x) y
    have hf(y:Site n):AtBase (F y):= AtBase.on_frame (b:=X) (fun i=>hp i.val) y
    exact ((hf _).mul (hp i.val)).mul (hf _|>.inv)
 have ha (x:E): O (Orb.liftLinks (b x)) = Orb.restrictedO O (Z x):=by
    have he: Orb.splitLink (X x) (Y x)=b x:=by funext i; unfold Orb.splitLink; split <;> rfl
    rw [← he,← ht.gauge (Orb.frame (X x)) (Orb.frame_neg (X x))];
    change O (Orb.aligned _ _)=_
    rw [Orb.alignment h]; rfl
 have h₁: Z 0=1:=funext fun i=>(hz i).starts
 have h₂: YM.Push.Loops.MatDiffAt Z 0:= fun i=> (hz i).smooth
 have h₃:Tendsto Z (𝓝 0) (𝓝 1):= by rw [← h₁]; exact h₂.continuousAt
 have he: (O ∘ Orb.liftLinks ∘ b) =ᶠ[𝓝 0] (Orb.restrictedO O ∘ Chart.expLinks G _) ∘ (down ∘ Z):=by
    filter_upwards [h₃.eventually down_right] with x hx
    exact (ha x).trans (congr_arg (Orb.restrictedO O) hx.symm)
 have hS:= ht.curved.germ; apply ContDiffAt.congr_of_eventuallyEq _ he
 apply ContDiffAt.comp (f:=down ∘ Z) _ _ ((down_chart h₂ h₁).of_le le_top)
 rwa [comp_apply,h₁,down_one]

lemma tree {R:Period}(T:R.Tree){O:Wilson.Config G R.side→ℝ}(h:Orb.PreTest O):
    ContDiffAt ℝ ∞ ((O ∘ R.restore ∘ T.drape) ∘ Chart.expLinks G T.Free) 0:=by
 let b:= T.drape ∘ Chart.expLinks G T.Free
 let f:=Reg.asOrb R ∘ b
 have hf(i:R.Link): AtBase (fun x:T.Free→G.Color=> b x i):= by
    by_cases ht:i∈T.edges
    · rw [show (fun x:T.Free → G.Color=> b x i)=(fun _=>1) from funext fun x=>T.drape_tree _ ⟨i,ht⟩]; exact AtBase.stay
    let j:T.Free:=⟨i,ht⟩; rw [show (fun x:T.Free → G.Color=> b x i)=(G.lieExp ∘ fun x=> x j) from funext fun x=> T.drape_free _ j]; exact AtBase.exp (contDiff_apply _ _ _|>.contDiffAt) rfl
 have hs(i:Orb.OEdge R.side):AtBase (fun x=> f x i):= by
    dsimp only [f,Reg.asOrb,comp_apply,Period.restore]; split_ifs
    · exact hf _
    exact (hf _).inv
 have he:(O ∘ R.restore ∘ T.drape) ∘ Chart.expLinks G T.Free= O ∘ Orb.liftLinks ∘ f:= funext fun x=> by simp only [Function.comp_apply,f,Reg.recover]; rfl
 rw [he]; exact adapt (even_iff_two_dvd.mpr R.even) h hs
end YM.FVA2.OrbGerm
