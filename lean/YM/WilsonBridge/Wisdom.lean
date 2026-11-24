import YM.WilsonBridge.Pin
import YM.X.Stems.Window
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.AveragedStep.Formal.Spiral
/-!
# Any bare Section cylinder + its homogeneous connection kernel in the MS algebra.

all translates, all ranks (not just leading), in the cover. Exact, not a smooth symbol
estimate. See `Pin` generation. Subsequent files prove leading symbol agrees including
midpoint convention. Does not include top W inverse yet.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonBridge.Wisdom
open Function Finset Filter Set
open PertExtension PositionX
open MS Book Koszul Cylinder Lab Native Native.Studio Sew MS.Theater
open Lattice Taylor Plane Native.Chart
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]
    {N:Type} {d i j:ℕ}{e:N→F}{s:Finset Cover}{n:Side}{p:Sector N}
lemma judge {f:F→ℝ}(h:germ f)(d:ℕ): ink e (PertExtension.Series.Radial.jet f d)= mask d (ink e f):= by
   induction d generalizing f with
   | zero =>
        rw [Nat.cast_zero,rank_zero_hat]; rw [show Series.Radial.jet f 0=(fun _=> f 0) from funext (fun i=> by simp [Series.Radial.jet])]; exact ink_const ..
   | succ d ih =>
        apply ext_D
        · rw [drip, strange _ (by simp; omega)]; unfold Series.Radial.jet; rw [show (iteratedFDeriv ℝ (d+1) f 0) (fun _=> (0:F))=0 from ContinuousMultilinearMap.map_coord_zero _ (0: Fin (d+1)) rfl,mul_zero,Complex.ofReal_zero] -- inspect
        · intro i; rw [inktip,conn, inktip, funext (show ∀ x:F, layer (e i) (Series.Radial.jet f (d+1)) x=_ from fun x=> AveragedStep.SD.radial_front f h d x _)]; rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]; exact ih (germ_layer h (e i))

local infixl:70 " ⋆ "=> product p
-- commuting subalgebra on bosonic polynomials; exponent by Cauchy product.
local notation "Χ"=> Draft.DotFlip (G:=G) (P:= Cover)
def port (i: Stems.Hair G):= formAt i.1.2 i.2 i.1.1
private def portκ (i: Stems.Hair G): Dark Χ := ⟨atLetter (port i),speaks_p (p:=Χ) (port i)⟩
variable (G) in
def coder: Stems.Curly G →ₐ[ℂ] ↥( Dark Χ ):= MvPolynomial.aeval portκ
variable (G) in
def walls: Stems.Curly G →ₗ[ℂ] Raw (LightMode G Cover) ℂ:= (( Dark Χ ).subtype).comp (coder G).toLinearMap
lemma wallsX (i: Stems.Hair G): walls G (MvPolynomial.X i)=atLetter (port i):= congr_arg Subtype.val (MvPolynomial.aeval_X portκ i)
lemma wallsC (x:ℂ): walls G (MvPolynomial.C x)=coin x:= Eq.trans (congr_arg Subtype.val (MvPolynomial.aeval_C (R:=ℂ) (f:=portκ) ..)) (cash1 ..)
lemma wallsM (u v: Stems.Curly G) : walls G (u*v) = product Χ (walls G u) (walls G v):= by change (coder G (u*v)).val=_; rw [map_mul]; rfl
lemma gets (u:Stems.Curly G): walls G u∈ Stack _ _:= by
   induction u using MvPolynomial.induction_on with
   | C x=> rw [wallsC]; exact (piece x).property
   | add x y hx hy=> rw [map_add]; exact (Stack _ _).add_mem hx hy
   | mul_X t j h=> rw [wallsM,wallsX]; exact (couple Χ (⟨_,h⟩:Dot G Cover) (single (port j))).property

def tattoo (G:Gauge): Stems.Curly G→ₗ[ℂ] Dot G Cover:= (walls G).codRestrict (Stack _ _) gets
lemma roof (u:Stems.Curly G): (tattoo G u).val=walls G u:= rfl
lemma tattoo_C (x:ℂ): tattoo G (MvPolynomial.C x)=piece x:= Subtype.ext (wallsC x)
lemma tattoo_X (i: Stems.Hair G): tattoo G (MvPolynomial.X i) = Cylinder.single (port i):= Subtype.ext (wallsX i)
lemma tattoo_M (u v:Stems.Curly G): tattoo G (u*v)=couple Χ (tattoo G u) (tattoo G v):= Subtype.ext (wallsM u v)

-- complex-linear extension (read real and imaginary parts); product with a real factor only needed
private def chain (e:N→F)(f:F→ℂ): Raw N ℂ:= ink e (Complex.re∘ f) + Complex.I • ink e (Complex.im ∘ f)
private lemma inkCL (f:F→ℝ): chain e (((↑):ℝ→ℂ)∘ f)=ink e f:= by rw [chain,show Complex.im∘(_∘f)=(0:F→ℝ) from rfl, ink_zero e, smul_zero,add_zero]; rfl
private lemma inkCC (x:ℂ): chain e (fun _=>x)=coin x:= by rw [chain, show Complex.re ∘ (fun _:F=>x)=(fun _=>x.re) from rfl, show Complex.im ∘ (fun _:F=>x)=(fun _=>x.im) from rfl, ink_const .., ink_const .. ]; funext l; cases l ; simpa [coin,mul_comm] using x.re_add_im; simp [coin]
private lemma inkCP {f g:F→ℂ}(hf:germ f)(hg:germ g): chain e (f+g)=chain e f+chain e g:= by
   rw [ chain, show Complex.re∘(f+g)= Complex.re∘ f+Complex.re∘ g from rfl, show Complex.im∘(f+g)=Complex.im∘ f+Complex.im∘ g from rfl, ink_add _ (f:=Complex.re ∘ f) (f':=Complex.re ∘ g) ( Complex.reCLM.contDiff.contDiffAt.comp 0 hf ) (Complex.reCLM.contDiff.contDiffAt.comp 0 hg), ink_add _ (f:=Complex.im ∘ f) (f':=Complex.im ∘ g) ( Complex.imCLM.contDiff.contDiffAt.comp 0 hf ) (Complex.imCLM.contDiff.contDiffAt.comp 0 hg),smul_add, chain,chain ]; abel
private lemma inkCR (he:∀ i,p i=true→e i=0){f:F→ℂ}{g:F→ℝ} (hf:germ f)(hg:germ g): chain e (fun t=> f t*(g t:ℂ))= chain e f ⋆ ink e g:= by
    rw [ chain,show Complex.re ∘ (fun t=> f t*(g t:ℂ))= (Complex.re ∘ f)*g from funext (by simp), show Complex.im ∘ (fun t=> f t*(g t:ℂ))= (Complex.im ∘ f)*g from funext (by simp), ink_mul _ (f:=Complex.re ∘ f) he ( Complex.reCLM.contDiff.contDiffAt.comp 0 hf ) hg, ink_mul _ (f:=Complex.im ∘ f) he ( Complex.imCLM.contDiff.contDiffAt.comp 0 hf ) hg,chain, map_add,map_smul ]; rfl

section Period
-- no offset shifts.S.Native periodic test; reads hair expansion.
variable (n)
abbrev V := Lot G (Edge (Site n))
def trace (u:V (G:=G) n): Stems.Brush G := expandAt 0 u
lemma traced (u:V (G:=G) n)(x:Edge Cover): trace n u x= u (wrap n x.1,x.2):= by unfold trace expandAt; rw [add_zero]
private def sees (i:Stems.Hair G): V ( G:=G ) n→L[ℝ] ℝ:= Native.projector ((wrap n i.1.1,i.1.2),i.2)
def cost (u:Stems.Curly G)(z: V (G:=G) n):= Stems.snap (trace n z) u
lemma costX (i:Stems.Hair G): cost n (MvPolynomial.X i) = fun z=> ( sees n i z:ℂ ):= by funext z; rw [cost,Stems.snap,MvPolynomial.aeval_X,sees, Native.projector_k, Stems.text, traced]
lemma costC (x:ℂ): cost ( G:=G ) n (MvPolynomial.C x)= fun _=>x:= by funext u; simp [cost,Stems.snap]
lemma costMat (u:Stems.Curly G) : germ (cost n u):= by
    induction u using MvPolynomial.induction_on with
    | C x=> rw [costC]; exact contDiffAt_const
    | mul_X p i ih=> rw [show cost n (p* MvPolynomial.X i)=cost n p*cost n (MvPolynomial.X i) from funext (fun x=> map_mul (Stems.snap (trace n x)) p _),costX]; exact ih.mul ( Complex.ofRealCLM.contDiff.comp (sees n i).contDiff |>.contDiffAt)
    | add p q h k=> rw [show cost n (p+q)=cost n p+ cost n q from funext (fun x=>map_add (Stems.snap (trace n x)) p q)]; exact h.add k
lemma native_I (i:Mind G (Site n)) : ink direction (Native.projector i (Q:=Edge (Site n)))=atLetter (formAt i.1.2 i.2 i.1.1) := by
    apply ext_D; · simp [atLetter] -- syntax
    intro x; rw [inktip, funext (show ∀ z:V (G:=G) n,layer (direction x) (Native.projector i) z = ( Native.projector i ) ( Native.direction x ) from fun z=> DFunLike.congr_fun ( Native.projector i ).fderiv _), ink_const]; rw [show Native.projector i (Native.direction x)= way (knot (id:(Edge (Site n))→Edge (Site n))) x i from ( knot_way id x i ),show formAt i.1.2 i.2 i.1.1 = knot id i from rfl ]; by_cases hv:x=knot id i; rw [hv,only,Complex.ofReal_one,hear ]; rw [need _ hv,Complex.ofReal_zero,unheard _ hv]; funext l; cases l <;> rfl
lemma home_T (u:Stems.Curly G): enters n (tattoo G u)=chain direction (cost n u):= by
    let p:= Draft.DotFlip (G:=G) (P:=Site n)
    induction u using MvPolynomial.induction_on with
    | C x=> rw [tattoo_C x,costC,inkCC]; exact coin_turn ..
    | add x y hx hy=> rw [ map_add, map_add, hx,hy, show cost n (x+y)=cost n x+cost n y from funext (fun _=> map_add (Stems.snap (trace n _)) x y), inkCP ( costMat .. ) ( costMat .. ) ]
    | mul_X t j h =>
        have hv : enters n ( Cylinder.single (port j) (R:=ℂ) )= ink direction (sees n j):= by change (Ferry (post (wrap n)) _).val = _; rw [escort,sees, native_I]; rfl
        rw [tattoo_M, tattoo_X, show enters n (couple Χ _ _)= product p (enters n (tattoo G t)) (enters n (Cylinder.single (port j))) from congr_arg Subtype.val (transport_comes ..), h,hv ]; rw [show cost n (t* MvPolynomial.X j)=cost n t*cost n (MvPolynomial.X j) from funext (fun _=>map_mul ( Stems.snap (trace n _) ) t _ ), costX ]; exact Eq.symm ( inkCR ( p:=p ) (fun i=> ( Native.glow G (Site n)).never i) ( costMat .. ) (sees n j).contDiff.contDiffAt )
end Period

open ProjectorNext.Calibration Source Wilson
variable {A:CoverConfig G→ ℝ} (hA:Small G A)
private def regionA:= hA.choose
def layerK :Dot G Cover:= Sew.art (G:=G) (A:=UsedEdges (regionA hA)) Subtype.val (Stems.kind (regionA hA) A)
def fixture (n:Side)(A:CoverConfig G→ℝ):Wilson.Config G n→ℝ:= fun U=> A (expandAt 0 U)
lemma as_eval (n:Side)(x: V ( G:=G ) n): (fixture n A ∘ nation) x= Stems.kind (regionA hA) A ( Sew.pull (thread (wrap n) (Subtype.val:UsedEdges (regionA hA)→Edge Cover)) x ):= by
    change A (Stems.posit (trace n x))=_; refine Stems.extend_eq hA.choose_spec (trace n x) _ ?_; funext i; exact traced _ _ _
include hA in
lemma gild (n:Side): germ (fixture n A ∘ nation):= by
    rw [funext (show ∀ x,(fixture n A∘nation) x=(Stems.kind (regionA hA) A∘ (Sew.pull (thread (wrap n) (Subtype.val:UsedEdges (regionA hA)→Edge Cover)))) x from as_eval hA n)]; let f:= Sew.pull (thread (wrap n) (Subtype.val:UsedEdges (regionA hA)→Edge Cover)) (G:=G); refine ContDiffAt.comp ( f:= f ) 0 ?_ f.contDiff.contDiffAt; rw [map_zero]; exact Stems.kinds hA.choose_spec
lemma gilded (n:Side): enters n (layerK hA)=reads (fixture n A ∘ nation):= by rw [layerK, enters_gorge _ _ (show germ (Stems.kind (regionA hA) A) from Stems.kinds hA.choose_spec)]; apply congr_arg _; exact (funext (as_eval hA n)).symm
lemma rated (n:Side)(x:V (G:=G) n)(k:ℕ): cost n (Stems.mark A hA k) x=(↑(Series.Radial.jet (fixture n A ∘ nation) k x):ℂ):= by
    rw [cost,Stems.mark_test]; apply congr_arg Complex.ofReal; exact (Series.Radial.homogeneous_derivative (fixture n A ∘ nation) x k ((gild hA n).of_le le_top)).symm
/-- The marks generated BEFORE quotient and momentum transforms. This is a cover equality at all perturbative orders. Hence also carries to arbitrary regulators. -/
theorem glyph_K (k:ℕ): model k (layerK hA)=tattoo G (Stems.mark A hA k):= by
    apply (enterEq ..).mp; refine Eventually.of_forall fun n=>?_ ; rw [show enters n (model _ _)=mask k (enters n (layerK hA)) from enterShim (b:=false) n k,gilded, home_T, funext (show ∀ x,cost n (Stems.mark A hA k) x=(((↑):ℝ→ℂ)∘(Series.Radial.jet (fixture n A ∘ nation) k)) x from fun x=> rated hA n x k), inkCL ]; exact (judge (gild hA n) k).symm

section Stamp
open PertExtension.Orb
open SlotEvaluation
variable {W:Labels.Frame G d}{S: SectionData W} {H:Hol G}
variable (h:S.Sound H)(P: Bid.pop S) (i:W.Index)
def coreK :Dot G Cover:= layerK (Stems.opt i h P)
lemma answers (n:Side): enters n (coreK h P i)= reads (fieldAt S i 0 ∘ nation):= gilded ..
lemma zoneK : From (coreK h P i).val (W.grades i).2:= by
    intro l hl; let h':= Stems.opt i h P; have hw: Stems.mark (Stems.evalS S i) h' l.length=0:= Stems.snap_ext (fun x=> by rw [Stems.mark_test,Stems.no_under x i h P (by omega),map_zero,Complex.ofReal_zero]); rw [← enough l (F:=(coreK h P i).val) rfl, ← mask_s (coreK h P i),coreK, glyph_K,hw,map_zero ]; rfl
include h in
private lemma goes_i (n:Side) : Native.Chart.OpenGauge (drive n) (fieldAt S i 0):= by
    intro g v; unfold fieldAt; rw [show siteGauge _ g v = Lattice.gauge (fun i=>(g i)⁻¹) v from ?_, S.placed_invariant h ]; funext l; unfold siteGauge Lattice.gauge; rw [inv_inv]; rfl
/-- Explicit realized Pin for off-shell bare basis (no top frame W yet). -/
def shoots : Pin G where
    power:=(W.grades i).2
    F:= coreK h P i
    func _:= fieldAt S i 0
    fixed n:= goes_i h i n
    smooth n:= gild ( Stems.opt i h P ) n
    packed _:= gilded ..
    low n:= from_pass n (zoneK h P i)
-- literal placement formula with offset
lemma shoots_at (n:Side)(z:Cover): (shoots h P i).charged n z= fieldAt S i (wrap n z):= by
    funext l; change fieldAt S i 0 _=_; unfold fieldAt; rw [show l∘offset (wrap n z)=Lattice.translate (wrap n z) l from ?_, SectionData.places_trans S,zero_add ]; funext j; change l (wrap n z + j.1,j.2)=l (j.1+ wrap n z,j.2); rw [add_comm]
theorem idealK : Aura (coreK h P i) (W.grades i).2 := ⟨zoneK h P i,Tune_port _ _ (show germ (Stems.kind (regionA (Stems.opt i h P)) (Stems.evalS S i)) from Stems.kinds (Stems.opt i h P).choose_spec),fun k=> ⟨ _, (shoots h P i).fixed k,(shoots h P i).smooth k,(shoots h P i).packed k⟩⟩
end Stamp
end YM.WilsonBridge.Wisdom
