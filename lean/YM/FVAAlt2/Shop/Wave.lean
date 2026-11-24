import YM.FVAAlt2.Shop.Poly
import YM.Comparison.Stencils.Corona.Ride
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
/-!
# Tone law for microscopic Wilson stencils
bridge to the native LPT top Wick corrected prescription at its OWN horizon.
Fourier log-link plane waves turn local polynomials into the SAME native continuum-direction
perturbative tensors. Demonstrate highest-rank part of W^{-1} column at Taylor order zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source
open Planned.PrimaryIntegral295.Place
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT
open Comparison.Stencils (columnSeries cylinder)
open Comparison.Stencils.Symbols (symbol LocalPol Var patch inscribe coordinate)
open Comparison.Stencils.Corona
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open scoped Topology ContDiff
variable {G:Gauge}{d:ℕ}{n:Side}{F:Labels.Frame G d}(S : SectionData F)
local notation "W"=> Spot S.stencil
local notation "M"=> W × Conn G
local notation "D₀"=> Dev S.stencil G
local notation "L"=> (placeEdge (S:=S.stencil))
variable (j:F.Index)
local infix:70 " ⋄ "=> product ( hands G )
local notation "C₄"=> Mind G Cover
local notation "Θ"=> Lane4 G
local notation "p₄"=> hands G
abbrev Bord (G:Gauge): Type:= ↥(Theater.Dark (hands G))

/-- all positive link slots (no ghosts at the Mark). -/
def onew (i:C₄)(p:Θ):=Tone.paywave p (formAt i.1.2 i.2 i.1.1)
lemma sees_p (i:C₄)(p:Θ)(h:onew i p≠0): p.1=(Landau.gauge i.1.2,i.2):= Tone.in_light _ _ h
lemma simpleTie : Tie (pNo C₄) p₄ (fun p:Θ=>fun i=> onew i p):=fun i j h=> show false= Landau.parity j.1 from (sees_p i j h) ▸ rfl

def onevar (x:C₄): Bord G:= ⟨ mono (onew x),by
 intro w h; rcases w with _|⟨i,_|_⟩; exact rfl; swap; exact rfl; change onew x i=0; exact Classical.byContradiction (fun he=> h (by simp [hands,field,sees_p x i he]))⟩
abbrev wholeSpace (G:Gauge):= MvPolynomial (Mind G Cover) ℂ
def Ψ (G:Gauge): wholeSpace G→ₐ[ℂ] Bord G:= MvPolynomial.aeval onevar
def namesC (S:Finset Cover)(x:Var G S): Mind G Cover:= (placeEdge x.1,x.2)
def leaps (G:Gauge)(S:Finset Cover): LocalPol G S→ₐ[ℂ] wholeSpace G:= MvPolynomial.rename (namesC S)

lemma planTone (v:MvPolynomial M ℂ): Tone.run (Ferry (Sew.knot L) ( (region.symm (bos_poly M v).val )))=(Ψ G (leaps G S.stencil v)).val:=by
 let Y:=Ψ G; let E:=leaps G S.stencil; let K:Matrix Θ M ℂ:=fun i u=>onew (namesC S.stencil u) i; let p:=pNo M
 suffices he: FVAAlt2.pull K (bos_poly M v).val=(Y (E v)).val by rw [Tone.run,study, show (fun (i:Θ)(u:M)=>paywave i (Sew.knot L u))= K from rfl,eq_pull ]; exact he
 induction v using MvPolynomial.induction_on with
 | C j=> rw [ show bos_poly M (_)=algebraMap ℂ _ j from MvPolynomial.aeval_C ..,Com.alg_piece,Com.piece_val, pull_coin,show E _=MvPolynomial.C j from MvPolynomial.rename_C ..,show Y _=algebraMap ℂ _ j from MvPolynomial.aeval_C ..,Theater.cash1 ]
 | add P Q HP HQ=> rw [map_add,map_add,map_add, Submodule.coe_add, Submodule.coe_add,map_add, HP,HQ]
 | mul_X P i h=>
    have hT:Tie p p₄ K:=fun i a ht=> simpleTie (namesC S.stencil i) a ht
    rw [map_mul,map_mul,map_mul,Com.mul_val, pull_product hT,h,Theater.darkM,show E _=MvPolynomial.X _ from MvPolynomial.rename_X ..,show Y _=onevar _ from MvPolynomial.aeval_X ..,show bos_poly M _=Bos.letter _ from MvPolynomial.aeval_X ..]; congr 1;
    rw [Bos.letter_val]; funext l; rcases l with _ | ⟨a,_|⟨x,l⟩⟩; exact rfl; exact pull_atLetter ..; rw [pull_cons,Finset.sum_eq_zero]; rfl; intro j _; by_cases he:i=j; subst i; rw [hear,pull_coin]; exact mul_zero _; rw [unheard i (Ne.symm he),map_zero]; exact mul_zero _

variable {H:Hol G}(h:S.Sound H)
include h in
lemma valSense (i:ℕ) : Tone.run (Book.model i (origin S j))=(Ψ G (leaps G S.stencil (symbol S.stencil (cylinder S j) i))).val:=by
 rw [← planTone]; congr! 1; rw [port_poly S j h,origin,Sew.art,← mod_ferry]; rfl

def Pict (G:Gauge) : Primary G→ₐ[ℂ] wholeSpace G:=MvPolynomial.aeval (fun u:Crumb G=>Comparison.Stencils.Corona.act (Tally u.1) (fun x=>MvPolynomial.X (x,u.2)))
-- no membership unknown edge constraints. enlarge to full real arrays.
lemma Pict_real (x:Links ℤ G.Color)(p:Primary G): MvPolynomial.aeval (fun i :Mind G Cover=> (↑(x i.1 i.2):ℂ)) (Pict G p)= demonstrates x p:=by
 induction p using MvPolynomial.induction_on with
 | C p=> simp [Pict,demonstrates]
 | add x y hx hy=> rw [map_add,map_add,map_add,hx,hy]
 | mul_X p i h=> rw [map_mul,map_mul,h,map_mul, Pict,MvPolynomial.aeval_X, act_simple i.1.offset i.1.plaq]; unfold demonstrates; rw [MvPolynomial.aeval_X]; simp [map_add,map_sub,lanes,act_simple i.1.offset i.1.plaq]
lemma allegiance {S:Finset Cover}{v: Primary G}{p:LocalPol G S}(h:Binds v p):leaps G S p=Pict G v:=by
 apply poly_eq; intro l; let x:=fun e:Edge Cover=> WithLp.toLp 2 fun i=> l (e,i); let V:Links ℤ G.Color:= x
 rw [show Complex.ofReal ∘ l=(fun i:C₄=> (↑(V i.1 i.2):ℂ)) from rfl, Pict_real V v,leaps,MvPolynomial.aeval_rename]; exact h V
include h in
lemma read_base (hp:Bid.pop S): Tone.run (Book.levels (F.grades j).2 (origin S j) 0)= (Ψ G (Pict G ((topMatrix S H h hp).basis j))).val:= by
 unfold Book.levels; rw [Nat.cast_zero,zero_add,valSense S j h,allegiance (v:= (topMatrix S H h hp).basis j)]; simpa only [columnSeries,zero_add] using! plated j h hp
end YM.FVAAlt2.Shop
