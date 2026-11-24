import YM.Integration.WilsonPhysicalExteriorRunningRows

/-! Exact two-source observation under a coherent change of the
physical bulk and all field subtraction arguments. Both finite matrices
are genuine normalized Wilson readings on the very same torus and
two sites. All lower engineering rows are retained, including their
physical spacing powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFieldGram
open Finset Matrix Lattice Labels Source Precision MS MS.Land MS.Menus MS.Rake
open FVAAlt2 Lobby WilsonPhysicalExteriorRunningRows
open PowerSeries (C)
open scoped Classical Matrix BigOperators
variable {G:Gauge}{V:Frames G}{H:Hol G}{B:MS.Local.Physical.Deck G}{n:Side}
variable (D:ChartRatio G)(R:Registry V H)(Q:Prescription B)
local notation "PS" => PowerSeries ℂ

def pay (y z e:ℝ) (p:Label B) (a:Glyph B p.h):PS :=
  C (((e:ℂ)⁻¹)^p.h*(e:ℂ)^a.size)*coordinates Q p.h z y z (Land.read p.item) a

def padded {d:ℕ} (y z e:ℝ) (p:Label B) (a:Glyph B d):PS :=
  if h:a.size≤p.h then pay Q y z e p (MSFeeCoordinates.restrict a h) else 0

def change (d:ℕ) (y z e:ℝ) : Matrix (Glyph B d) (Glyph B d) PS :=
  fun p a=>padded Q y z e (owner p) a
def measure (x:Fin 2→Site n) (e y:ℝ) (p q:Label B):PS :=
  newEra D R Q y ![p,q] x e
def pair (d H:ℕ) (x:Fin 2→Site n) (e y:ℝ):Matrix (Glyph B d) (Glyph B H) PS :=
  fun a b=>measure D R Q x e y (owner a) (owner b)

private theorem original {W:Type} [LinearOrder W] [Fintype W]
    (p:W→Label B)(y z e:ℝ)(he:e≠0)(x:W→Site n):
    newEra D R Q z p x e =
    ∑ a:(i:W)→Glyph B (p i).h,(∏i:W,pay Q y z e (p i) (a i))*
      reprice Q.team y z (newEra D R Q y (fun i=>owner (a i)) x e) := by
  have H:=WilsonPhysicalExteriorRunningRows.measured D R Q p (fun _=>z) (fun _=>e) y z e x
    (fun _=>he) he
  have hr:WilsonPhysicalExteriorSlotReference.ratio (fun _:W=>e) e p=1:=by
    simp [WilsonPhysicalExteriorSlotReference.ratio,div_self (Complex.ofReal_ne_zero.mpr he)]
  rw [WilsonPhysicalExteriorSlotReference.aligned D R Q p z e _ x he (fun _=>he),hr,map_one,one_mul] at H
  rw [H,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _=>?_
  have hc:(∏ i:W,C (((e:ℂ)⁻¹)^(p i).h*(e:ℂ)^(a i).size)) =
    C (WilsonPhysicalExteriorSlotReference.engineering (fun _:W=>e) p)*
      C ((e:ℂ)^wt (fun i=>owner (a i))) := by
    rw [←map_prod,←map_mul,WilsonPhysicalExteriorSlotReference.engineering,Finset.prod_mul_distrib,
      wt,←Finset.prod_pow_eq_pow_sum]
    rfl
  simp only [pay,Finset.prod_mul_distrib,hc]
  ring

private theorem measured (p q:Label B) (y z e:ℝ) (he:e≠0) (x:Fin 2→Site n) :
    measure D R Q x e z p q =
      ∑ a:Glyph B p.h, ∑ b:Glyph B q.h, pay Q y z e p a * pay Q y z e q b *
        reprice Q.team y z (measure D R Q x e y (owner a) (owner b)) := by
  let pp:Fin 2→Label B:=![p,q]
  let β:Fin 2→Type:=fun i=>Glyph B (pp i).h
  let f:β 0 × β 1→PS:=fun ab=>pay Q y z e p ab.1*pay Q y z e q ab.2*
    reprice Q.team y z (measure D R Q x e y (owner ab.1) (owner ab.2))
  change newEra D R Q z pp x e=_
  rw [original D R Q pp y z e he x]
  calc
    _ = ∑ ab:β 0×β 1, f ab := by
      apply Fintype.sum_equiv (piFinTwoEquiv β); intro a
      rw [Fin.prod_univ_two]
      change _*reprice Q.team y z (newEra D R Q y (fun i=>owner (a i)) x e)=
        _*reprice Q.team y z (newEra D R Q y ![owner (a 0),owner (a 1)] x e)
      congr 4; funext i;fin_cases i <;> rfl
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

private def fit {d:ℕ} (p:Label B) (h:p.h≤d) :
    Glyph B p.h ≃ {a:Glyph B d // a.size≤p.h} where
  toFun a:=⟨MSFeeCoordinates.extend h a,MSFeeCoordinates.remaining a⟩
  invFun a:=MSFeeCoordinates.restrict a.val a.property
  left_inv _:=rfl
  right_inv _:=rfl

private theorem portfolio {d:ℕ} (p:Label B) (h:p.h≤d) (y z e:ℝ) (F:Glyph B d→PS) :
    ∑a:Glyph B d,padded Q y z e p a*F a =
    ∑a:Glyph B p.h,pay Q y z e p a*F (MSFeeCoordinates.extend h a) := by
  let a (w:Glyph B d):PS:=padded Q y z e p w * F w
  have chosen:(∑w,a w)=∑w:{w:Glyph B d//w.size≤p.h},a w.val := by
    rw [←Finset.sum_subtype (p:=fun w:Glyph B d=>w.size≤p.h)
      (s:=Finset.univ.filter (fun w:Glyph B d=>w.size≤p.h)) (by simp)]
    exact (Finset.sum_subset (Finset.filter_subset ..) (by
      intro w _ no
      have hn:¬w.size≤p.h:=by simpa using no
      simp [a,padded,hn])).symm
  change (∑w,a w)=_
  rw [chosen,←Equiv.sum_comp (fit p h) (fun w=>a w.val)]
  refine sum_congr rfl fun w _=>?_
  change padded Q y z e p (MSFeeCoordinates.extend h w)*F (MSFeeCoordinates.extend h w)=_
  simp [padded,MSFeeCoordinates.remaining w,MSFeeCoordinates.extend,MSFeeCoordinates.restrict]

/-- The actual rectangular charged Gram identity, independently finite in
the two horizons and valid at every actual pair of microscopic sites. -/
theorem rectangular (d H:ℕ) (y z e:ℝ) (he:e≠0) (x:Fin 2→Site n) :
    pair D R Q d H x e z =
    change Q d y z e * (pair D R Q d H x e y).map (reprice Q.team y z) *
      (change Q H y z e).transpose := by
  apply Matrix.ext;intro p q
  rw [show pair D R Q d H x e z p q=measure D R Q x e z (owner p) (owner q) from rfl,
    measured D R Q _ _ y z e he x]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  have p0:(owner p).h≤d:=MSFeeCoordinates.remaining p
  have q0:(owner q).h≤H:=MSFeeCoordinates.remaining q
  let f (a:Glyph B d) (b:Glyph B H):PS:=
    reprice Q.team y z (measure D R Q x e y (owner a) (owner b))
  change _=∑a:Glyph B d,∑b:Glyph B H,(padded Q y z e (owner p) a*f a b)*padded Q y z e (owner q) b
  calc
    _=∑a:Glyph B (owner p).h,pay Q y z e (owner p) a*
      (∑b:Glyph B (owner q).h,pay Q y z e (owner q) b*
        f (MSFeeCoordinates.extend p0 a) (MSFeeCoordinates.extend q0 b)) := by
      refine sum_congr rfl fun a _=>?_
      rw [Finset.mul_sum];refine sum_congr rfl fun b _=>?_
      change _= _*(_*reprice Q.team y z (measure D R Q _ _ _ (owner a) (owner b)))
      ring
    _=∑a:Glyph B d,padded Q y z e (owner p) a*
      (∑b:Glyph B H,padded Q y z e (owner q) b*f a b) := by
      rw [portfolio Q (owner p) p0]
      refine sum_congr rfl fun a _=>?_
      rw [portfolio Q (owner q) q0]
    _=_:=by
      refine sum_congr rfl fun a _=>?_
      rw [Finset.mul_sum];refine sum_congr rfl fun b _=>?_;ring

end YM.Integration.WilsonPhysicalExteriorFieldGram
end
