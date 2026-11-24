import YM.FVAAlt2.Shop.Menus
import YM.FVAAlt2.Continuum
import YM.FVAAlt2.Plus.Conserv
/-!
# The starting Wilson perturbative series (at points)
Top inversion quotient moments with engineering factors removed,
stripped W_N-corrected columns. `Plan.begins` additionally uses
profiles (at ALL points) and engineering factors. We extend here by complex-linearity when
using Ω: real/imag still on real gauge fields. Real physical labels lifted to pure dims h & r
are specified by Deck. Use RBook & Λ to apply *one* coupled adjustment to all labels. Quantitative result
at this precise engineer unit normalization stated in next module. Later Deck
from Loft (`FormalOPE.RG10/Position`) and profile bindings to `Plan.begins`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Lobby
open Function Finset Filter Topology Lattice Labels Source
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Dial MS.Tide MS.Swirl MS.Swirl.Near MS.Fleet
open PowerSeries (C coeff)
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT Precision Shop Billing SchemeRG11.Sway SchemeRG11.Sway.Lam
open scoped Topology BigOperators ContDiff PowerSeries
variable {G:Gauge}{d k:ℕ}{n:Side}{B:MS.Local.Physical.Deck G}{Q:Deck G} {L:Frames G}{H:Hol G}
-- Lit.Inventory (avoid repeated reproduction in endpoints)
structure Registry (L:Frames G)(H:Hol G) where
 use (d:ℕ): SectionData (L.level d)
 owns (d:ℕ): (use d).Sound H
 bid (d:ℕ): Bid.pop (use d)

variable {W:Type} [LinearOrder W] (D: ChartRatio G) (R:Registry L H) (a: Cover) (x: W→ Cover)
abbrev Table (R:Registry L H)(B: Deck G): RichBook B:= richBook B L H R.use R.owns R.bid
def owner (v:Glyph B d): Rake.Label B:= ⟨v.size,⟨v.2.1,v.2.2⟩⟩
local notation "V"=> Rake.Label B
abbrev JLit (L:Frames G)(v:Rake.Label B):= (L.level v.h).Index
def γ (v:Rake.Label B)(i:JLit L v): ℂ:= valueP B (R.use v.h) (R.owns _) (R.bid _) v.item.2 i
def poster (v:V)(p:Site n)(i:JLit L v): Wilson.Config G n→ ℝ:= fieldAt (R.use _) i p
def slots (v:Rake.Label B)(i:JLit L v) := ((L.level v.h).grades i).2
local notation "c₁"=> Table R B
local notation "PSc"=> PowerSeries ℂ
local notation "TX"=> fun i:W=> wrap n (a+x i)
set_option linter.unusedSectionVars false

variable [Fintype W]
-- removed engineering factors. Incoming W weight v.h all. `Wilson_C^pt` (
-- unscaled prescription at coupling $g^N$). For Lean top $x,origin$ use periodic array.
abbrev ΦbaseT {S:W→Type}[∀ i,Fintype (S i)] (m:Finset W) (F:∀ i:W,S i→ ℕ)(O:∀ i:W,S i→Wilson.Config G n→ℝ)(u:(i:W)→ S i) : PSc:= PowerSeries.mk (fun k=> (↑(Fixed.treeMom D (∏ i∈m,O i (u i)) (∑ i∈m,F i (u i)) k):ℂ))
def WilsonPoint (n:Side)(x:W→Site n)(p:W→Rake.Label B) : PSc:=
  ∑ u:(i:W)→JLit L (p i), C (∏ i:W,γ R (p i) (u i))* ΦbaseT D univ (fun i:W=>slots (L:=L) (p i)) (fun i=> poster R (p i) (x i)) u

variable (K:MS.Land.Prescription B)(y:ℝ)(p:W→Rake.Label B)
open Book.Program Ends
local notation "Pf"=> Program.shift K.team y -- need scope
local notation "τ"=> K.team
local notation "κ"=> ApplyMPl c₁ ( Stripped τ ) K p

def redo (t:ℕ→ Program.Plan) (y:ℝ) :PSc →ₗ[ℂ] PSc where
 toFun f:= PowerSeries.mk (substitute (Program.shift t y) (unpack f))
 map_add' f g := by
    ext1 k; rw [map_add (coeff k),PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_mk,show unpack (f+g)=unpack f+unpack g from funext (fun i=>map_add (coeff i) _ _),map_add]; rfl
 map_smul' k f:= by ext1 i; rw [PowerSeries.coeff_mk,PowerSeries.coeff_smul,show unpack (k•f)=k•(unpack f) from funext (fun i=>PowerSeries.coeff_smul ..),map_smul,PowerSeries.coeff_mk]; rfl

def prepare (n:Side)(x:W→Site n) : PSc:=∑ v:(i:W)→ Glyph B (p i).h, (∏ i, bore p K y i (v i)) * redo τ y (WilsonPoint D R n x (fun i=> owner (v i)))
local notation "U"=> prepare D R K y p n TX
-- flat formulation (needed Triangle.PayReg)
abbrev markS (p:W→Rake.Label B)(L:Frames G)(i:W):= Σ (j:Glyph B (p i).h), JLit L (owner j)
def pay (i:W) (v: markS p L i):PSc:= C (γ R (owner v.1) v.2)* bore p K y i v.1
def σ (i:W)(v:markS p L i) := slots (owner v.1) v.2
def σO (n:Side)(x:W→Site n)(i:W)(v:markS p L i) := poster R (owner v.1) (x i) v.2
def plain (n:Side)(x:W→Site n) : PSc:=∑ u:(i:W)→ markS p L i,(∏ i, pay R K y p i (u i))* redo τ y (ΦbaseT D univ (σ (L:=L) p) (σO R p n x) u)
-- reshuffle prices. order finite, test table p
lemma pieclub (x:W→Site n): plain D R K y p n x=prepare D R K y p n x:=by
 let f:=fun (u:(i:W)→ markS p L i)=> redo τ y (ΦbaseT D univ (σ (L:=L) p) (σO R p n x) u); let J:=Glyph B∘(fun i:W=> (p i).h)
 let E: (Σ (u: ∀ i:W,Glyph B (p i).h), (i:W)→ JLit L (owner (u i)))≃((i:W)→markS p L i):={ toFun:=fun p i=>⟨p.1 i,p.2 i⟩, invFun:=fun p=>⟨fun i=>(p i).1,fun i=>(p i).2⟩, left_inv:=fun _=>rfl,right_inv:=fun _=>rfl }
 unfold prepare WilsonPoint plain; rw [ ← Equiv.sum_comp E (fun u=>(∏ i:W,pay R K y p i (u i))*f u),Fintype.sum_sigma]; simp_rw [map_sum,Finset.mul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; unfold pay; rw [Finset.prod_mul_distrib];
 let c:=∏ k:W,γ R (owner (i k)) (j k); let v(k:W): markS p L k:= (E ⟨ i,j⟩ k); let y':=∏ k:W,bore p K y k (i k); let z:=ΦbaseT D univ (σ (L:=L) p) (σO R p n x) v
 change (∏ k:W,PowerSeries.C (γ R (owner (i k)) (j k))) * y' * redo τ y z=y'*redo τ y (PowerSeries.C c * z)
 rw [← map_prod PowerSeries.C (fun k:W=>γ R (owner (i k)) (j k)),show PowerSeries.C c*z = c • z from (PowerSeries.smul_eq_C_mul ..).symm, map_smul,PowerSeries.smul_eq_C_mul]; change (PowerSeries.C c : PSc)*_*_= _; ring

lemma scal_C {E:Type} [AddCommGroup E][Module ℂ E](p:PSc)(c:ℂ)(u:ℕ→ E): scalS p (c • u)=scalS (C c*p) u:=by
 unfold scalS; rw [map_smul];
 rw [ show unpack (C c*p)=c • (unpack p) from funext (fun i=> PowerSeries.coeff_C_mul ..),map_smul];rfl
lemma permit (i:W) : κ i y= ∑ u:markS p L i, scalS (pay R K y p i u) (substitute (Program.shift τ y) (priceS (R.use _) u.2)):=by
 let Θ(i:W)(g:Glyph B (p i).h):= substitute Pf ( (Table R B).menu g.size g.grade g.2.2 );
 rw [show κ i y=∑ j:χ p i, scalS (bore p K y i j) (Θ i j) from ?_ ]; swap
 · funext k; change Menus.rentPl c₁ (Stripped τ) _ _ _= _; unfold Menus.rentPl; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun w _=>?_ ; unfold Θ scalS; rw [paired]; simp_rw [Glyph.preamblePl,bore,unpack,strip_wobble,PowerSeries.coeff_mk]; rfl
 conv_rhs=> rw [Fintype.sum_sigma]
 refine sum_congr rfl fun j _=>?_; unfold Θ; rw [ show (Table R B).menu j.size j.grade j.2.2 = ∑ i:JLit L (owner j),γ R (owner j) i • priceS (R.use _) i from rfl,map_sum ]; unfold scalS; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul]; exact scal_C (bore p K y _ _) (γ R _ _) (substitute Pf (priceS _ _))

def dum (v:Rake.Label B) : Σ j:Glyph B v.h,JLit L (owner j):=⟨ MS.Land.read v.item,0⟩
local notation "w"=> pay R K y p
-- prove at all positions no profile required. honest finite normalized Wilson series at all insertions
lemma paysHere (hn:Pert.Orb.Admissible n)(h:LocalRatio D): PhysicalSum G τ y n true (univ:Finset W) x a κ (Ends.unpack U):= by
 set s:=univ (α:=W); let T(i:W):= markS p L i; let df(i:W):T i:= dum (p i); let O:= σO R p n TX; let F:=fun (i:W) (j:markS p L i)=> origin (R.use _) j.2; let Ξ:=σ (L:=L) p; letI: Module.Free ℝ (SchemeRG11.Sway.Land G n):= Module.Free.of_divisionRing ℝ (SchemeRG11.Sway.Land G n); let A:=Module.finBasis ℝ (SchemeRG11.Sway.Land G n); let S:= Module.finBasis ℝ (ScalarGhost G n)
 suffices he: prepare D R K y p n TX=treeReg s τ y Ξ O w df D by
    rw [he]; refine PayReg h A S κ s τ y x a F Ξ O w (fun i j=>field_ok (R.use _) j.2 (R.owns _) (R.bid _) (TX i)) df (permit R K y p) (fun i k=> (billRentPl c₁ (Stripped τ) (K.fees (p i).h (p i).item) |>.actual k y).symm) ?_ hn; intro i k; exact ⟨ _, Menus.rentLimitPl c₁ (Stripped τ) (K.fees _ _) y k ⟩
 let X(i:(s:Type _)): i.1∈s:= i.property; let E: ((i: (s:Type _))→ markS p L i.1)≃((i:W)→markS p L i):= {
   toFun:= pad s df
   invFun:=fun f i=> f i.1
   left_inv:=fun i=>funext (fun j=> (dif_pos j.property : pad s df i j.val=i j))
   right_inv:=fun u=>funext fun i=> dif_pos (by simp [s]) }
 symm; rw [←pieclub]; unfold treeReg plain; apply Fintype.sum_equiv E; intro u; refine congr_arg₂ (·*·) rfl ?_; unfold κpoint redo; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; apply congr_arg PowerSeries.mk; exact congr_arg (substitute Pf) (funext (fun i=>by rw [unpack,ΦbaseT,PowerSeries.coeff_mk]; rfl))
end YM.FVAAlt2.Lobby
