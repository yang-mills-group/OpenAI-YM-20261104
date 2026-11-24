import YM.X.Plate.Grain
import YM.X.Shelf.Finite
import YM.X.Site.Ocean
/-!
# Criteria for admission in polynomial shell, ∗bounded rank∗. Control prospects by testing with leaving line A_t. interpolate any complex evaluation later via bone shutters.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Plate
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Shelf
open Ocean
open Stems hiding X
open scoped Topology ContDiff Classical BigOperators
variable {V W I:Type*} {p s: poly V}{t:V→ℂ}{a:ℂ}{k m n:ℕ}{G:Gauge}
-- test in one variable λ plus basepoint perturb, all χ included via complex B coercion
local notation "Ψ"=> poly Unit
def rider (x y: V→ℂ): Normal.poly V →ₐ[ℂ] Ψ := aeval (fun i:V=> C (x i) + C (y i)*X ())
variable (x y: V→ℂ)
lemma racer (r:ℂ)(p:poly V): aeval (fun _=>r) (rider x y p)=aeval (x+r • y) p:= by
    apply DFunLike.congr_fun (f:=(aeval (fun _=>r)).comp (rider x y)); ext1 i; simp [rider,mul_comm]
lemma lance (h:duty p k):duty (rider x y p) k:= h.affine _ (fun i=>by rw [rider,aeval_X]; exact (duty.base (k:=1) _).add ((duty.base (k:=0) _).mul (duty.x _)))
lemma rides (p:poly V): rider x y (slit y p)= slit 1 (rider x y p):= by
   induction p using MvPolynomial.induction_on with
   | C a=> simp [rider]
   | add p q h t=> simp_rw [map_add,h,t]
   | mul_X p i h=> rw [mul_comm p, slit_prod]; rw [map_mul (f:=rider x y) _ p,Derivation.leibniz]; simp only [smul_eq_mul,map_add,map_mul,h]; unfold rider; simp; ring -- name simp large
lemma glimpse (p:Ψ)(h:∀ r:ℝ, aeval (fun _=>(↑r:ℂ)) p=0):p=0:= by
   apply MvPolynomial.funext_set (fun _ : Unit=> Set.range Complex.ofReal) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective); intro x hx; obtain ⟨r,hr⟩:=hx () (show ()∈Set.univ from Set.mem_univ ()) -- x : Unit→ℂ
   rw [← show (fun _:Unit=> (↑r:ℂ))=x from funext (fun u=> by cases u; exact hr)]; exact (h r).trans (map_zero (aeval _)).symm
lemma would {f:ℕ→poly V}{x y:ℕ→V→ℂ}(h:∀ i,duty (f i) k)(hv:∀ r:ℝ, Released (fun i=> aeval (x i+(r:ℂ) • y i) (f i))): Released (fun i=> aeval (x i) (slit (y i) (f i))):= by
    let A i:= rider (x i) (y i) (f i); let E(r:ℝ):= (aeval (fun _ :Unit=> (r:ℂ)): Ψ →ₐ[ℂ] ℂ).toLinearMap; let Y:= (aeval (fun _ : Unit=> (0:ℂ)): Ψ→ₐ[ℂ]ℂ).toLinearMap; let s:= restrictTotalDegree Unit ℂ k; let W:= fun i=> aeval (x i) (slit (y i) (f i));
    have he : A∈ Badge Ψ Released s:= plenty (P:=crew) E s (fun p _=> glimpse p) A (fun i=>(mem_restrictTotalDegree _ _ _).mpr (lance (x i) (y i) (h i))) (fun r=> by change Released (fun i=> aeval _ (rider _ _ _)); simp_rw [racer];exact hv r)
    have hh : ∀ (L:Ψ→ₗ[ℂ]ℂ), Released (fun i=>L (A i)):= by
       intro L; clear hv h; generalize A=B at *; induction he using Submodule.span_induction with
       | mem p h=> obtain ⟨a,p,h,hp,rfl⟩:=h; simp_rw [map_smul];exact breaths h (constell (L p))
       | zero=> exact (by simp_rw [Pi.zero_apply,map_zero];exact Released.zero)
       | add a b _ _ x y=> simp_rw [Pi.add_apply,map_add]; exact x.add y
       | smul a b h t=> simp only [Pi.smul_apply,map_smul]; exact breaths (constell a) t
    have hk (i:ℕ):W i= (Y.comp (slit 1).toLinearMap) (A i):= by change _=aeval _ (slit 1 _); unfold W A; rw [←rides,racer]; simp
    change Released W; rw [show W=_ from funext hk]; apply hh
-- inserting control power
variable {q:ℕ+} {r:ℝ}
local notation "H"=> Hair G
structure Apt (q:ℕ+)(r:ℝ)(p:ℕ→ Curly G): Prop where
    price : ∃ k:ℕ,∀ i:ℕ,duty (p i) k
    use (A:ℕ→Brush G)(h:Tide q r A) : Released (fun i=> snap (A i) (p i))
namespace Apt
variable {f g:ℕ→ Curly G}
lemma stamp (h:Apt q r f)(A:ℕ→Brush G)(hp:Tide q r A) : Apt q r (fun i=> stroke (A i) (f i)):= by
    obtain ⟨k,hk⟩:= h.price; refine ⟨⟨k,fun i=> duty.slit_p (hk i)⟩,fun B he=>?_⟩; refine would hk (fun p=>?_);
    let c (A:Brush G): Hair G→ℂ:= (fun i=>Complex.ofReal (text A i)); let w:= B+p • A; have he(i:ℕ) : c (w i)= c (B i)+(p:ℂ) • c (A i):= by unfold w; funext j; change (↑(text (B i + p • A i) j):ℂ) = (text (B i) j:ℂ)+(p:ℂ)*(text (A i) j); unfold text; push_cast; simp only [Pi.add_apply,Pi.smul_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]; push_cast;rfl
    change Released (fun i=> aeval (c (B i)+(p:ℂ) • c (A i)) (f i)); simp_rw [← he]; exact h.use w ((by assumption: Tide q r B).up (hp.zoom p)) -- parser
lemma add (h:Apt q r f)(hp:Apt q r g):Apt q r (f+g):= by obtain ⟨k,x⟩:= h.price; obtain ⟨d,y⟩:= hp.price; refine ⟨⟨max k d,fun i=> duty.add ((x i).more (by simp)) ((y i).more (by simp))⟩,fun A hA=>?_⟩; simp_rw [Pi.add_apply,map_add]; exact (h.use A hA).add (hp.use A hA)
lemma up (h:Apt q r f)(a:ℕ→ℂ)(ha:Released a): Apt q r (fun i=> a i • f i):= by obtain ⟨k,H'⟩:=h.price; refine ⟨⟨k,fun i=> (H' i).scalar _⟩, fun A Hx=>?_⟩; simp_rw [map_smul]; exact Shelf.breaths ha (h.use A Hx)
lemma base : Apt q r (G:=G) 1:= by refine ⟨⟨0,fun i=>duty.one⟩,fun A he=>?_⟩; simp only [Pi.one_apply,map_one]; exact constell 1
end Apt
end YM.PositionX.Plate
