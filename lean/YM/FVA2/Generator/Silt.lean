import YM.FVA2.Generator.Solve2
/-!
# Assembly of the complete V3 stamp with ordinary Wick contractions (open):
first motion bill is zero on the diagonal. All physical marks and every Taylor file,
not merely one survey selected via the annulus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Seals.Foster
open Function Set Filter XSpace Pages Center Circuits XSpace.Trace XSpace.Lows XSpace.Mu XSpace.Chart2 Gland MeasureTheory Borders
open Lattice XSpace.Gland
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}
-- Sum over ordered slots removed. rehearsal at Tile, then attendance after axes.
abbrev FaceG (G:Gauge):= Addr G × MultiplierEstimates G

def rehearsal (p:MultiplierEstimates G)(f: FaceG G → Tile G): Tile G:= ((Pages.slip p).map f).sum
private lemma refill (p:MultiplierEstimates G)(P Q:FaceG G → Tile G): rehearsal p (fun i=>P i+Q i)=rehearsal p P+rehearsal p Q:=by unfold rehearsal; generalize slip p=L; induction L with | nil=> simp | cons i L ih=> simp only [List.map_cons,List.sum_cons,ih]; abel
private lemma onto (p:MultiplierEstimates G)(X:Tile G)(P:FaceG G→ Tile G): X * rehearsal p P=rehearsal p (fun i=>X* P i):=by unfold rehearsal; generalize slip p=L; induction L with | nil=> simp | cons i L ih=> simp only [List.map_cons,List.sum_cons,mul_add,ih]
private lemma bookable (p:MultiplierEstimates G)(f:Axis→Axis→FaceG G→Tile G){v:Submodule ℂ (Tile G)}(h:∀ u∈slip p,(∑ i:Axis,∑ j:Axis,f i j u)∈ v): (∑ i:Axis,∑ j:Axis,rehearsal p (f i j))∈v:=by
    unfold rehearsal; generalize hw:slip p=L at *; clear hw; induction L with
    | nil=> simp
    | cons u L ih=> simp_rw [List.map_cons,List.sum_cons,Finset.sum_add_distrib]; exact v.add_mem (h u (by simp)) (ih (fun z hz=> h z (by simp [hz])))
-- tally each row form
variable (p:MultiplierEstimates G)(x y z:Bond G)
def one : Tile G:= rehearsal p (fun i=> gem i.1 x * right y * right z * Pages.left i.2)
def two : Tile G:= rehearsal p fun i=> rehearsal i.2 fun j=> debit x y z i.1 j.1 j.2
def three : Tile G:= rehearsal p (fun i=> rehearsal i.2 fun j=> rehearsal j.2 fun k=>gem i.1 x * gem j.1 y * gem k.1 z * Pages.left k.2)
private lemma cost (p:MultiplierEstimates G)(u:List (Bond G))(x:Bond G): binder p (x::u)= right x*binder p u+rehearsal p (fun i=> gem i.1 x * binder i.2 u):= freight ..
-- use canon o/b allocation only to commute the prefactors outside sheets. Avoid simp loops.
private lemma move (x y z:Tile G)(p:MultiplierEstimates G) : x*(y*(z*Pages.left p))=x*y*z*Pages.left p:= by rw [mul_assoc,mul_assoc]
lemma tally : binder p [x,y,z]= right x * right y * right z * Pages.left p+one p x y z+one p y x z+one p z x y+two p x y z+two p x z y+two p y z x+three p x y z:=by
    unfold one two three debit; simp only [cost,closed,mul_add,onto,refill,move]
    simp_rw [show ∀ q:Addr G,right x*right y*gem q z =gem q z*right x * right y from (fun i=> by rw [mul_comm, mul_assoc]), show ∀ (q r: Addr G),right x*gem q y* gem r z=gem q y*gem r z *right x from (fun _ _=> by rw [mul_assoc,mul_comm]), show ∀ q r:Addr G,gem q x*right y* gem r z=gem q x*gem r z * right y from fun _ _=> mul_right_comm .., show ∀ q:Addr G,right x * gem q y =gem q y * right x from fun _=>mul_comm .. ]
    ac_rfl

variable {ι:Type}{L: Filter ι} [L.IsCountablyGenerated]{a:ι→ℝ} (S:Tendsto a L (𝓝 0))(ha:∀ᶠ i in L,0<a i)
variable (χ:Shade.Cut)(s:ℝ)(hs:0<s) (A:Maxwell.TaylorTower G)
include S ha hs
-- general family bond: polar cost uniform if ∀i. use ANY ordering for K1 and K3.
variable (X Y Z:Axis→ Axis → Bond G)(h:∀ i j:Axis,(X i j).fee.cost+(Y i j).fee.cost+(Z i j).fee.cost=4)
include h
lemma zero1 (hp:wage p=d): (∑ i:Axis,∑ j:Axis,one p (X i j) (Y i j) (Z i j))∈ None L a χ s (Bracket.seat d A):= by
    unfold one; apply bookable; intro u hu; obtain hr:= Pages.accounted hu; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> solo S ha χ s hs _ _ _ _ _ _ (h i j) (by omega)
lemma zero3 (hp:wage p=d): (∑ i:Axis,∑ j:Axis,three p (X i j) (Y i j) (Z i j))∈ None L a χ s (Bracket.seat d A):= by
    unfold three; apply bookable; intro u hu; apply bookable; intro v hv; apply bookable; intro w hw; obtain h₁:= Pages.accounted hu; obtain h₂:=Pages.accounted hv; obtain h₃:=Pages.accounted hw; exact Submodule.sum_mem _ fun i _=>Submodule.sum_mem _ fun j _=> occupied S ha χ s hs _ _ _ _ _ _ _ _ (h i j) (by omega)
omit h
lemma zero2 (θ:RG12.Strike.Farm) (X Y Z:G.ColorIndex)(hp:wage p=d): (∑ i:Axis,∑ j:Axis, two p (lea θ i j X) (peal θ i j Y) (free θ i j Z))∈ None L a χ s (Bracket.seat d A):= by
    unfold two; apply bookable; intro u hu; apply bookable; intro v hv; exact Borders.certified S ha χ s hs u.1 v.1 v.2 θ X Y Z A (by have ht:= Pages.accounted hu; have hs:= Pages.accounted hv; omega)
-- exact orientation, choose fields x y z.
theorem supplied (u v t:G.ColorIndex)(hp:wage p=d): (∑ i:Axis,∑ j:Axis, binder p (axes u v t i j))∈ None L a χ s (Bracket.seat d A):= by
    let k:=None L a χ s (Bracket.seat d A); let x(i j:Axis):= Bond.mk [i] j u; let y (i _j:Axis):= Bond.mk [] i v; let z (_i j:Axis):= Bond.mk [] j t
    unfold axes; simp_rw [tally,Finset.sum_add_distrib]; apply k.add_mem; apply k.add_mem; apply k.add_mem; apply k.add_mem; apply k.add_mem; apply k.add_mem; apply k.add_mem; exact k.sum_mem fun i _=> k.sum_mem fun j _=> Seals.empty S ha χ s hs _ p (x i j) (y i j) (z i j) rfl hp
    exact zero1 p S ha χ s hs A x y z (fun _ _=> rfl) hp
    exact zero1 p S ha χ s hs A y x z (fun _ _=> rfl) hp
    exact zero1 p S ha χ s hs A z x y (fun _ _=> rfl) hp
    -- ensure $θ$ in curly; one `rfl`.
    exact zero2 p S ha χ s hs A .alpha u v t hp
    exact zero2 p S ha χ s hs A .beta u t v hp
    exact zero2 p S ha χ s hs A .delta v t u hp
    exact zero3 p S ha χ s hs A x y z (fun _ _=> rfl) hp
end YM.FVA2.Generator.Seals.Foster
