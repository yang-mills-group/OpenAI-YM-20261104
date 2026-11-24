import YM.WilsonComparison.Finite.Vertices
import YM.AlbaMS.Barr.Earning

/-!
# Gauge invariant source dictionary

Concrete microscopic stencils from the supplied MS `Dressed` Wilson prescription. Not
arbitrary polynomials assigned to labels. In particular we can fix it once for all
volumes, arities, positions, and coupling orders. These are real stencils, finite linear
combinations of genuine covariantized curvature-difference monomials (Haar color averaged).
They are physical fields PRIOR to frame/position calibrations. A lift satisfying the
actual `Fits` condition for **every** `raw` basis element in `Deck`. This does not claim
that every such choice satisfies the stronger section/frame conventions of Part IV;
we keep the general field-input interface for that comparison. We do not identify them
with (e.g.) a bare column after Wick subtraction just from `Fits`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Lattice Precision
open MS MS.Landau MS.Koszul MS.Native MS.Native.Orient MS.Cylinder MS.Native.Chart
open MS.Local MS.Local.Physical MS.Native.Studio MS.Lifting MS.Swirl MS.Swirl.Near
open MSBar MSBar.Loft MSBar.Bric MSBar.Odom MSBar.Inlay
open MS.Cylinder.Lab MS.Menus Bric.Coil
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {K : ChartRatio G} {n b k : ℕ}

-- general interface. `F` includes stencil at the origin. same coupling/rank data
-- on the top cover. `O` evaluable by both prescriptions. Used with a fixed input (such as
-- the concrete constructor using PlaquetteRecipe below), not an existence reprovisioning
-- at each n. Laurent exponent and independent site/coupling dictionary explicitly typed.
structure Stencil (G : Gauge) (b : ℕ) where
  F : Dot G Cover
  O : (n : Side) → Site n → Wilson.Config G n → ℝ
  continuous : ∀ (n : Side) (x : Site n), Continuous (O n x)
  reads : ∀ n x, Reads (shown n (Lab.Shift x F)) (O n (wrap n x))
  invariant (n:Side) (x:Site n) : OpenGauge (drive n) (O n x)
  low : MS.Book.From F.val b
  phase : Tuned F 0

/-- Concrete recipe. `b` for these Dressed stencils is the number of
 curvature/jet factors (independent of lattice units etc.).
-/
inductive PlaquetteRecipe (G : Gauge) (b : ℕ)
 | mono (f : Fin b → Plaq) (u : Grid G b)
 | zero
 | plus (a c : PlaquetteRecipe G b)
 | scale (r:ℝ) (a : PlaquetteRecipe G b)

namespace Stencil
variable (x : Stencil G b) (m : Side)

lemma aura : Aura x.F b := ⟨x.low,x.phase,fun n=> ⟨x.O n 0, x.invariant n 0,
  (by simpa only [map_zero] using (x.reads n 0).born), by
    change _ = Native.reads _
    convert (x.reads n 0).home using 1
    · rw [shift_nil]; rfl
    rw [map_zero] ⟩⟩

abbrev luster (w:Cover) : Inlay.Net.Luster (deck m) G where
  integrand:= x.O m (wrap m w)
  smooth:= (x.reads m w).born
  solid:=fun u t=> by
    rw [homedeck]; rw [show Lattice.gauge t u=siteGauge (drive m) t⁻¹ u from ?_, x.invariant];
    ext1 j; unfold Lattice.gauge siteGauge; simp only [Pi.inv_apply, inv_inv]; rfl
lemma kSign_ne (i:Atom Axis) : kSign i≠0:=by unfold kSign; split <;> simp
lemma signs_ne {ι:Type} (l:List ι) (f:ι→ℂ)(h:∀ i,f i≠0): (l.map f).prod≠0:= by induction l with|nil=>exact one_ne_zero|cons i l ih=>exact mul_ne_zero (h i) ih
lemma from_shaded {r:ℤ} {A B:Type} {U:Cyl A ℂ} (he:MS.Book.From U.val r) (T:B→A→ℂ): MS.Book.From (shade T U) r := by
  intro l hv; rw [← MS.Book.enough (F:=shade T U) l rfl,← MS.Book.mod_ink]
  have ht : MS.Book.model l.length U=0 := by
    apply Subtype.ext; ext k
    change MS.Book.mask _ _ k=0
    by_cases hk:k.length=l.length
    · rw [MS.Book.enough k (by omega : (k.length:ℤ)=l.length)]; exact he k (by omega)
    exact MS.Book.strange k (by omega)
  rw [ht,map_zero]; rfl
lemma rankFunding (A: Cover) : needy b (Inlay.bare (I:=Site m) (x.luster m A).caseG) := by
  intro l h; by_contra! ht
  let K:=tagPosition G (Site m)
  let V := Inlay.bare (I:=Site m) (x.luster m A).caseG
  let Z : Orbit.FixedMode G m→ℂ := fun i=> kSign i.1.1
  have hv : siteSymbol (Wind ø Complex.ofRealHom V)= enters m (Shift A x.F):= by
    unfold V; rw [real_analytic]; exact (x.reads m A).home.symm
  have he': MS.Book.From (Shift A x.F).val b:= from_shaded x.low _
  have hz:= MS.Book.from_pass m he' (l.map K) (by rw [List.length_map]; omega)
  rw [← hv,siteSymbol_read,show (l.map K).map (tagPosition G (Site m)).symm=l from ?_] at hz
  · change ( ( (l.map K).map Z).prod * Complex.ofReal (V l))=0 at hz
    exact (mul_ne_zero (signs_ne _ Z (fun i=> kSign_ne _)) (Complex.ofReal_ne_zero.mpr h)) hz
  simp [K,List.map_map]

def pace (A:Cover) : Barr.Pace (deck m) G := ⟨x.luster m A,b,x.rankFunding m A⟩
-- Thus this *actual stencil* is usable, no Aura placeholder needed in the bridge.
lemma same_source (i:ℕ) (c A:Cover) :
    let V:= x.pace m (A+c); symbols (Orbit.σbranch (G:=G) (n:=m)) ℂ
      (encodeMomentum (Wind ø Complex.ofRealHom (rankn (i+b) (Inlay.bare (I:=Site m) V.intent.caseG)))) =
    Mark_T G m A c (MS.Book.levels b x.F i) := by
  dsimp only; rw [symbols_encode, ← rank_wind,siteSymbol_rank, real_analytic];
  rw [show Taylor.ink direction (x.pace m (A+c)).intent.caseG.val=enters m (Shift (A+c) x.F) from (x.reads ..).home.symm, ← with_anchor]; congr 1
  rw [show MS.Book.mask _ (enters _ _)= enters m (MS.Book.model ((i+b:ℕ):ℤ) (Shift _ _)) from (MS.Book.enterShim false m _).symm]
  rw [MS.Book.levels,Lab.Shift, transport, MS.Book.mod_ferry]; norm_cast
end Stencil

namespace PlaquetteRecipe
private lemma ad_cont : Continuous (fun p : G.El×G.Color => G.adjoint p.1 p.2) := by
  change Continuous (fun p : G.El×G.Color=> G.projectColor (G.mat p.1 * G.colorMat p.2 * star (G.mat p.1)))
  fun_prop (disch:= first | apply LinearMap.continuous_of_finiteDimensional)
private lemma curvature_continuous (m:Side) (x:Site m) (s:PlaqAxes) (u:List Axis): Continuous (fun U: Wilson.Config G m=> edgeSense (drive m) s u x U) := by
  induction u generalizing x with
  | nil=> unfold edgeSense Native.Studio.tip bolt₀ atCart; fun_prop
  | cons i l ih=> exact (ad_cont.comp (f:=fun U:Edge (Site m)→G.El=> (U (x,i),edgeSense (drive m) s l (x+Lattice.step i) U)) ((continuous_apply _).prodMk (ih _))).sub (ih x)
private lemma real_cont (m:Side) (x:Site m) (f: Fin b→Plaq)(u:Grid G b) : Continuous (realF (drive m) b x f u) := by
  rw [show realF (drive m) b x f u=fun V=> ∑ i: Grid G b, (MS.Lifting.group G i u • monF (drive m) b x f i) V from funext (fun V=> by rw [realF,Finset.sum_apply])]; apply continuous_finsetSum; intro i _; apply Continuous.const_smul; unfold monF; apply continuous_finsetProd; intro j _
  unfold ropeF; split_ifs with h h'; · exact (α (i j)).continuous.comp (curvature_continuous ..)
  · exact ((α (i j)).continuous.comp (curvature_continuous ..)).neg
  exact continuous_const

def primary (f:Fin b→ Plaq)(u:Grid G b): Stencil G b where
  F:= markP b f u
  O n x:= realF (drive n) b x f u
  continuous n x:= real_cont n x f u
  reads n x:=by
    rw [shown,trans_shift,markP,sings_go (g:=drive n) _ _ (Native.Orient.atlas n), map_zero, Lab.Shift,
      sings_go (g:=drive n) _ _ (fun i j=> (add_assoc ..).symm), add_zero]
    exact real_R ..
  invariant n x g U := sings ..
  low:= (real_A b f u).low
  phase:= (real_A b f u).phase

def eval : PlaquetteRecipe G b → Stencil G b
 | mono f u => primary f u
 | zero=> ⟨0,fun _ _=>0,fun _ _=>continuous_const,by
      intro n x; rw [map_zero,map_zero]; refine ⟨contDiffAt_const,?_⟩; change 0= Taylor.ink _ 0; rw [Taylor.ink_zero],fun _ _ _ _=>rfl,(Aura.zero G _).low,(Aura.zero G b).phase⟩
 | plus x y=> {
      F:= x.eval.F+y.eval.F
      O:= x.eval.O+y.eval.O
      continuous n i:= (x.eval.continuous n i).add (y.eval.continuous n i)
      reads n i:=by rw [map_add,map_add]; let F:=x.eval.reads n i; let H:=y.eval.reads n i; refine ⟨F.born.add H.born, ?_⟩; rw [add_stack,F.home,H.home]; exact (Taylor.ink_add direction F.born H.born).symm
      invariant n i g U:= congr_arg₂ (·+·) (x.eval.invariant n i g U) (y.eval.invariant n i g U)
      low:= (x.eval.aura.add y.eval.aura).low
      phase:= (x.eval.aura.add y.eval.aura).phase }
 | scale r x=> {
      F:= (r:ℂ) • x.eval.F
      O:= r • x.eval.O
      continuous n i := (x.eval.continuous n i).const_smul r
      reads n i:=by rw [map_smul,map_smul]; exact (x.eval.reads n i).cash r
      invariant n i g U:= congr_arg (r • ·) (x.eval.invariant n i g U)
      low:= (x.eval.aura.scalar r).low
      phase:= (x.eval.aura.scalar r).phase }

open MS.Book Plane Color Tensor Local Submodule
lemma selects {v:ℤ} {r:ℕ} (B:Deck G) (i:B.BIndex v r): ∃ P:PlaquetteRecipe G r, MS.Lifting.Fits P.eval.F (B.raw v r i) r v false := by
  refine span_induction (p:=fun H _=>∃ P:PlaquetteRecipe G r, MS.Lifting.Fits P.eval.F H r v false) ?_ ⟨zero,MS.Lifting.Fits.zero _⟩ ?_ ?_ (syntaxK (B.le (B.form v r i)))
  · rintro y ⟨f,u,rfl,h,rfl⟩; exact ⟨.mono f u, mark_F r f u⟩
  · intro a d h k H K; obtain ⟨A,hA⟩:=H; obtain ⟨D,hD⟩:=K; exact ⟨A.plus D,hA.add hD⟩
  intro c H hF h; obtain ⟨F,h⟩:=h; exact ⟨scale c F,h.smul (c:ℂ)⟩
end PlaquetteRecipe

/-- shared stencil material. Later analyses may request a more specialized Dictionary -/
structure Dictionary (B: Deck G) where
  cylinder (u v:ℕ) (_: B.BIndex u v): Stencil G v
  classical_jet (u v:ℕ)(i): MS.Lifting.Fits (cylinder u v i).F (B.raw u v i) v u false

namespace Dictionary
def standard (B:Deck G): Dictionary B where
  cylinder _ _ i:= (PlaquetteRecipe.selects B i).choose.eval
  classical_jet _ _ i:= (PlaquetteRecipe.selects B i).choose_spec

def asLit {B:Deck G} (D:Dictionary B): LitBook B:= ⟨fun u v i=> (D.cylinder u v i).F,fun u v i=> (D.cylinder u v i).aura,D.classical_jet⟩
end Dictionary
end YM.WilsonComparison.Finite
