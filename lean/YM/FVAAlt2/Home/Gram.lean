import YM.FVAAlt2.Home.Landmark
import YM.FormalOPE.RG10.Horizon.Survey
/-!
# Positive spectral rank of all lower slot horizons as needed for MS adjustment.
No high OPE Gram assumed. ArcPair.B matrix can be multiplied (right) even using
 unreflected (left) vs test. Orthogonality by SLOT count at zeroth formal order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Report
open Function Set Finset Filter Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater MS.Land
open MeasureTheory Matrix
open RG10.Apertures (land pane Halo Valid)
open PowerSeries (C coeff constantCoeff)
open Profiles Maxwell.Wick Maxwell.Wick.Occ
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge}{L:Frames G}{B:MS.Local.Physical.Deck G}{M:Booked B}{H:Source.Hol G}
variable {d n:ℕ}
set_option linter.unusedSectionVars false
local notation "F"=> Glyph B d
local notation "Ym"=> RG10.Position.Deck L d
local notation "Kn"=> Finsupp.weight (letterCount (G:=G))
section frame
variable {X T R: Type*} [Fintype X][Fintype T][CommSemiring R]
abbrev qr (t:Test 2) (i j:X): Datum X:= ⟨⟨2,t⟩,![i,j]⟩
def layerP (t:Test 2) (f:Datum X→ R): Matrix X X R:= Matrix.of fun i j=>f (qr t i j)
lemma swatch (t:Test 2)(f:Datum X→R)(D:Matrix T X R): layerP t (mix f D) = D * layerP t f * Dᵀ:=by
 apply Matrix.ext; intro i j; unfold layerP mix; rw [Matrix.of_apply];
 -- proof after template `FormalOPE/RG10/Horizon/Matrix`
 let P(p:X×X):= f (qr t p.1 p.2)*(D i p.1*D j p.2)
 calc
   _ = ∑ p:X×X,P p:= Fintype.sum_equiv (finTwoArrowEquiv X) _ _ (fun x=>by
      change f ⟨⟨2,t⟩,x⟩*_ = f ⟨⟨2,t⟩,![x 0,x 1]⟩* _; congr 1
      · exact congr_arg (fun x=> f (⟨⟨2,t⟩,x⟩: Datum X)) (by ext1 i; fin_cases i <;> rfl)
      change (∏ i':Fin 2,D (![i,j] i') (x i')) = _; simp [Fin.prod_univ_succ])
   _ = _:= by rw [Fintype.sum_prod_type]; simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Finset.sum_mul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i hi; unfold P; dsimp only; ring
end frame
abbrev Book (p:Powers G 2) (i:Fin 2):= {v:Occ p // v.label=i}
lemma measuring (p:Powers G 2)(i:Fin 2): Fintype.card (Book p i)=Finsupp.weight letterCount (p i):= by
 let s:=(p i).support
 let U:= Σ j:s,Fin (p i j.val)
 let W:=Book p i
 let f : U→W:= fun j=> ⟨ atSlot i j.1.val j.2.val j.2.isLt,rfl⟩
 have hv:Surjective f:=by
    rintro ⟨ ⟨⟨a,j,x⟩,h⟩,ha⟩; change a=i at ha; subst i
    change x < p a j at h; exact ⟨⟨ ⟨j,Finsupp.mem_support_iff.mpr (by omega)⟩, ⟨ x,h⟩⟩ ,rfl⟩ -- tactic
 have hh: Injective f:=by
    rintro ⟨ ⟨a,ha⟩,⟨x,hx⟩⟩ ⟨⟨b,hb⟩,⟨y,hy⟩⟩ he; have hc:a=b:=congr_arg (fun i:W=>Occ.probe i.val) he; subst b; have hh:x=y:=congr_arg (fun i:W=>Occ.index i.val) he; subst y; rfl
 rw [ ← Fintype.card_congr ( Equiv.ofBijective f ⟨hh,hv⟩ ) ]; unfold U s; simp [Finsupp.weight_apply,Finsupp.sum,letterCount]; exact Finset.sum_attach ..
lemma numEq {p:Powers G 2}(w: Matching p): Fintype.card (Book p 0)= Fintype.card (Book p 1):= by
   have he(x:Book p 0): Occ.label (partner w x.val)=1:= by have ht := different w x.val; rw [x.property] at ht; apply Fin.ext; omega
   have hx(x:Book p 1): Occ.label (partner w x.val)=0:= by have ht := different w x.val; rw [x.property] at ht; apply Fin.ext; omega
   exact Fintype.card_congr ( f:={ toFun x:=⟨_,he x⟩, invFun x:=⟨ _,hx x⟩, left_inv x:=Subtype.ext (Occ.turn w _), right_inv x:=Subtype.ext (Occ.turn w _) }) -- `e` binder
lemma stepNone (u v: WickPol G) (x:Points 2)(hi:Length u d)(hv:Length v n)(ht:d≠n): Wick.moment G x ![u,v]=0:= by
 rw [Wick.sumFormula]; apply Finset.sum_eq_zero; intro i he
 obtain hm0:= Finsupp.mem_support_iff.mp ((Fintype.mem_piFinset.mp he) 0); obtain hm1:=Finsupp.mem_support_iff.mp ((Fintype.mem_piFinset.mp he) 1)
 let H0:=hi (show u.coeff (i 0)≠0 from hm0); let H1:=hv (show v.coeff (i 1)≠0 from hm1)
 have hh : IsEmpty (Matching i):= ⟨fun p=> ht (Eq.trans H0.symm ((measuring i 0).symm.trans ((numEq p).trans ((measuring i 1).trans H1))))⟩
 rw [Wick.monomial,Fintype.sum_empty,mul_zero]
variable (L B)
lemma meter (p:Glyph B d): Length (writes L d (mast B d L p)) p.grade:= fun i hi=>congr_arg Prod.snd ((weight_collapse i).symm.trans (pegFrame (L:=L) p hi)) -- bicart
lemma stepOff(t:Test 2)(p q: F)(h:p.grade ≠ q.grade): wickY L (mast B d L) (qr t p q)=0:=by
   unfold wickY; let f(i):=writes L d (mast B d L i); have ht(x:Points 2): wickB L (mast B d L) (![p,q]) x=0:=by
      rw [wickB]; change Wick.moment G x (fun i=> f (![p,q] i))=_; rw [show (fun i:Fin 2=> f (![p,q] i))=![f p,f q] from funext (fun i=>by fin_cases i <;> rfl)]; apply stepNone _ _ _ (meter L B p) (meter L B q) h
   change (∫ x:Points 2,t x * wickB L (mast B d L) (![p,q]) x)=_; simp_rw [ht,mul_zero,integral_zero] -- notation issue

variable {B} (S:MS_Data G M) (μ:ℝ)
abbrev freeJ (d:ℕ): Datum (RG10.Position.Deck L d)→ℝ:= Physical.free (L:=Maxwell.standard L) (RG10.Position.deck L d)
local notation "φ"=> freeJ L
lemma holly: mix (constantCoeff ∘ (currentM (d:=d) μ S)) (dout L B d)=freeJ L d:=by
 have H:=funext (fun v:Datum (RG10.Position.Deck L d)=> physics L μ S v); calc
    _= constantCoeff ∘ mix (currentM (d:=d) μ S) ((dout L B d).map C):= Eq.symm (by rw [mixPap,Matrix.map_map]; rfl)
    _=_ := H
lemma holy_rail(t:Test 2): layerP t (freeJ L d) = (dout L B d)*layerP t (constantCoeff ∘ currentM (d:=d) μ S)*(dout L B d)ᵀ:=by rw [← swatch, holly]
lemma oldStar: constantCoeff ∘ currentM (d:=d) μ S= mix (freeJ L d) (din L B d):=by rw [←holly L S μ,mix2,din_mul,mix1] -- order?
include L
lemma white (t:Test 2)(p q:F)(h:p.grade≠ q.grade): layerP t (constantCoeff ∘ currentM (d:=d) μ S) p q=0:= by change constantCoeff (currentM μ S (qr t p q))=0; rw [dawnM L μ S (p:=qr _ _ _), stepOff L B _ _ _ h];rfl
lemma fulldet(d:ℕ):∃ t:Test 2,(layerP t (constantCoeff ∘ currentM (d:=d) μ S)).det≠0:=by
 obtain ⟨T,ht⟩:= RG10.Apertures.shines L d
 let t:=T.shape; refine ⟨t,?_⟩; let X:= layerP t (freeJ L d); have h:X.det≠0:= by intro H; apply ht; unfold pane; rw [Matrix.det_mul,show RG10.Apertures.land L d T=X from rfl,H,zero_mul]
 -- left= # invertible across non-square dimensions? Din not square; determinant multiplication fails unless dims equal; use IsUnit via exact 2-sided basis.
 let U:=dout L B d; let V:=din L B d; let Y:=layerP t (constantCoeff ∘ currentM (d:=d) μ S); have HX:X= U * Y * Uᵀ:= holy_rail ..; have he: V*U=1:=din_mul .. ; have hv: U * V=1:= dout_mul ..
 let Φ:= (Uᵀ* X⁻¹)*U; suffices ht : Y*Φ=1 by intro h0; apply (zero_ne_one (α:=ℝ)); rw [← Matrix.det_one (n:=Glyph B d), ← ht, Matrix.det_mul,h0,zero_mul]
 calc Y*Φ = (V*X*Vᵀ)*Φ:= by congr 1; rw [HX, ← Matrix.mul_assoc,← Matrix.mul_assoc, he, one_mul, Matrix.mul_assoc Y,← Matrix.transpose_mul,he,transpose_one, Matrix.mul_one ] -- goal matrix simplify with matrix assoc manually
      _= _ := by
        rw [show V*X*Vᵀ*Φ= V*(X*(Vᵀ*Uᵀ)*X⁻¹)* U from (by unfold Φ; simp_rw [Matrix.mul_assoc]), ← Matrix.transpose_mul,hv,transpose_one, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),Matrix.mul_one,he]
end YM.FVAAlt2.Home.Report
