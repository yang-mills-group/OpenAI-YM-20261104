import YM.PertExtension.SliceCurl

/-! Reexpression of tree Gaussian covariances in terms of any full-cover gradient
solve at the two images. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.PertExtension.LatticePT
namespace Projection
open Function Finset Lattice Orbit Orb GaussianScore
open scoped Classical Topology BigOperators RealInnerProductSpace
variable {G : Gauge}{n : Side}

abbrev SheetLink (G : Gauge)(n:Side):= Links (Per n) G.Color
abbrev FaceAt (n : Side):= Face (Per n)
def fold (n:Side)(p:FaceAt n) : FaceAt n:=(-p.1-step p.2.val.1-step p.2.val.2,p.2)
lemma fold_twice (p:FaceAt n): fold n (fold n p)=p:=Prod.ext (by unfold fold; dsimp only;abel) rfl

def folded (G:Gauge)(n:Side)(B:SheetLink G n) : SheetLink G n:= fun e=> -B (reflect e)
def crease (G : Gauge)(B:SheetLink G n)(p:FaceAt n):G.Color:=Curl B p.1 p.2.val.1 p.2.val.2
lemma crease_fold (B:SheetLink G n)(p:FaceAt n) : crease G (folded G n B) p= crease G B (fold n p):=by
   unfold crease folded fold Curl reflect;dsimp only
   have h₁ (x : Site n)(i j): -(x+step i)-step j=(-x-step i-step j):= by abel
   have h₂ (i j)(x:Site n):-x-step i-step j+step i=-x-step j:=by abel
   rw [h₁,h₁,h₂]; abel
lemma crease_add (A B:SheetLink G n) (p:FaceAt n): crease G (A+B) p=crease G A p+crease G B p:=by unfold crease Curl;simp only [Pi.add_apply];abel

def Costates (B:SheetLink G n)(y:FaceAt n)(ξ:G.Color):Prop:= ∀ A:SheetLink G n, (∑ p:FaceAt n, Inner.inner ℝ (crease G B p) (crease G A p))= Inner.inner ℝ ξ (crease G A y)
lemma fold_symmetric (Y X:FaceAt n→ℝ) (h:∀ p, X p=Y (fold n p)) : ∑ p:FaceAt n,X p=∑ p:FaceAt n,Y p:=by
  let e:FaceAt n≃FaceAt n:=⟨fold n,fold n,fold_twice,fold_twice⟩
  exact (Finset.sum_congr rfl fun i _=> h i).trans (Equiv.sum_comp e Y)

-- same dual on actual tree space, joint score uses half area

def signal (y:FaceAt n)(ξ:G.Color): Module.Dual ℝ (Dir G n) := (innerSL ℝ ξ).toLinearMap ∘ₗ letterPolar (G:=G) y
lemma signal_eq (p ξ)(A:Dir G n):signal p ξ A=Inner.inner ℝ ξ (letterPolar p A):=rfl
variable (even:Even n.val)
include even
theorem pair_use {X:SheetLink G n}{y:FaceAt n}{ξ:G.Color}(h:Costates X y ξ) :
   let A:=(saddle even).inverse (signal y ξ)
   ∀ p:FaceAt n,letterPolar p A= crease G X p+crease G X (fold n p):=by
    let P:= X+folded G n X
    obtain ⟨U,hU⟩:=(all_loaded even <| show Mirrors P from fun e=> by
      change X _+ -X _=-(X _+ -X _);rw [reflect_reflect];abel)
    have he (p) : letterPolar p U=crease G X p + crease G X (fold n p):=
         (show Curl _ _ _ _ = _ from (hU p.1 p.2.val.1 p.2.val.2).trans <| (crease_add X (folded G n X) p).trans (congr_arg (fun v=>crease G X p+v) (crease_fold X p))) -- syntax
    have hc:scoreDual U=signal y ξ := by
       apply LinearMap.ext; intro B;change score U B= _
       have hR' : variation B=folded G n (variation B):=funext fun e=> by
            change variation B e = -variation B _; rw [variation_invert even,neg_neg]
       have hz p : letterPolar p B=letterPolar (fold n p) B:= by
            change crease G (variation B) p=crease G (variation B) (fold n p);nth_rw 1 [hR'];apply crease_fold
       let D (p:FaceAt n):= Inner.inner ℝ (crease G X p) (letterPolar p B)
       have hp:∑ p:FaceAt n,D p = signal y ξ B:= h (variation B)
       unfold score
       simp_rw [he,inner_add_left]
       rw [Finset.sum_add_distrib,(fold_symmetric D _ (fun p=> congr_arg (fun x=> Inner.inner ℝ (crease G X (fold n p)) x) (hz p)))]
       change ((∑ p,D p)+ _)/2= _;rw [hp];ring
    change ∀ p,letterPolar p ((saddle even).inverse (signal y ξ))=_
    rw [show (saddle even).inverse (signal y ξ)=U from (by rw [←hc]; exact Law.solves ..)]
    exact he
lemma wick_uses (X:SheetLink G n)(p y ξ η)(h:Costates X y ξ):
    (saddle even).wick (signal y ξ) (signal p η) = Inner.inner ℝ η (crease G X p + crease G X (fold n p)):= by rw [Law.wick,signal_eq,pair_use even h]

end Projection
end YM.PertExtension.LatticePT
