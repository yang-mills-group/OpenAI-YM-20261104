import YM.XSpace.Compat.GaussInverse
import YM.XSpace.Encore
import YM.XSpace.Coin

/-!
# Wick composition in the cover diagram array

`tie` on open *Wick symbols*. `Book` price for two-vertex states.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mu
open Lattice Trace Chart2 JetGauge Contraction MvPolynomial Function Set Finsupp Next.Rank.Normal Outline
open scoped Topology BigOperators
variable {G:Gauge} {I:Type*} {d e: ℕ}
abbrev Stamp (G:Gauge) := St ℤ G
abbrev root (G:Gauge):JetGauge.Cov (Bone G ℤ):= duskCov G

def freeze: Module.End ℂ (Stamp G):= milk (-root G)
def flicker : Module.End ℂ (Stamp G):=milk (root G)
@[simp] lemma gone (v:Stamp G): flicker (freeze v)=v:=by unfold freeze flicker; rw [warms, Symmetric.cancels, froze]
@[simp] lemma came (v:Stamp G): freeze (flicker v)=v:= YM.XSpace.Compat.thaw ..
lemma no_twins : Injective (freeze (G:=G)):=LeftInverse.injective (g:=flicker) gone
lemma no_twin : Injective (flicker (G:=G)):=LeftInverse.injective (g:=freeze) came
@[simp] lemma nothing_frozen : freeze (G:=G) 1=1:=pure _
@[simp] lemma nothing_huge : flicker (G:=G) 1=1:=pure _
abbrev part (A:Scale.Tape G.Color): Module.End ℂ (Stamp G):= (D (G:=G) A).toLinearMap
lemma ripple (L: Line G) (v:Stamp G) : flicker (harp L*v)= harp L*flicker v + flicker (part (G:=G) (bake L) v):= by unfold flicker harp; rw [refresh,reveal,skims];rfl
lemma winter (L:Line G)(v:Stamp G): freeze (harp L*v) = harp L*freeze v - part (G:=G) (bake L) (freeze v):=by
  apply no_twin; rw [gone, map_sub,ripple, gone, add_sub_cancel_right]
lemma slip (A:Contact G)(p:Stamp G): freeze (D A p)=D A (freeze p):=(skims ..).symm
@[simp] lemma leg (L:Line G): flicker (harp L)=harp L:=by simpa [part] using ripple L 1
lemma free_leg (L:Line G): freeze (harp L)=harp L:= by apply no_twin; rw [gone,leg]

def tieR (x: Stamp G) : Module.End ℂ (Stamp G):= flicker ∘ₗ (LinearMap.mulLeft ℂ (freeze x)) ∘ₗ freeze
def tie (G:Gauge) : Stamp G →ₗ[ℂ] Module.End ℂ (Stamp G) where
  toFun := tieR
  map_add' x y:= by apply LinearMap.ext; intro z; change flicker (freeze (x+y)*freeze z)=_; rw [map_add,add_mul,map_add];rfl
  map_smul' c x:=by apply LinearMap.ext; intro z; change flicker (freeze (c • x)*freeze z)=_; rw [map_smul,smul_mul_assoc,map_smul]; rfl
lemma tie_ap (x y:Stamp G): tie G x y= flicker (freeze x*freeze y):=rfl
lemma out (x y:Stamp G): freeze (tie G x y)=freeze x* freeze y:=by rw [tie_ap, came]
lemma tie_one (x:Stamp G):tie G x 1=x:=by rw [tie_ap,nothing_frozen,mul_one,gone]
lemma one_tie (x:Stamp G): tie G 1 x=x:=by rw [tie_ap,nothing_frozen,one_mul,gone]
lemma flip (x y: Stamp G): tie G x y=tie G y x:=by rw [tie_ap,mul_comm,← tie_ap]
lemma method (x y z:Stamp G): tie G x (tie G y z)=tie G (tie G x y) z:=by apply no_twins; simp only [out,mul_assoc]
lemma cross_rule (x y:Stamp G)(v:Line G): tie G (harp v*x) y= harp v*tie G x y + tie G x (D (bake v) y):=by
  apply no_twins; rw [out, winter, map_add,winter,out,out,sub_mul,slip]; let f:=D (bake v); change _-(f (freeze x))*freeze y = _-(f (freeze x*freeze y))+_
  rw [f.leibniz]; simp only [smul_eq_mul]; unfold f; ring
lemma jet (v:Contact G)(x y:Stamp G): D v (tie G x y)=tie G (D v x) y+tie G x (D v y):=by
  apply no_twins; simp only [map_add, slip,out,(D v).leibniz,smul_eq_mul]; ring
lemma shifted (x:Cover)(p q:Stamp G):Trace.volume x (freeze p)=freeze (Trace.volume x p):= by apply no_twin; unfold flicker; rw [meant]; simp only [← show flicker=milk (root G) from rfl]; rw [gone,gone]
lemma bring (x:Cover)(p q:Stamp G): tie G (Trace.volume x p) (Trace.volume x q)=Trace.volume x (tie G p q):=by apply no_twins; rw [out,← shifted x p p,← shifted x q q,← shifted x _ q, out,map_mul]

abbrev scalar (G:Gauge) := pit (G:=G) (0: Scale.Tape G.Color)
lemma counts (p:Stamp G): scalar G p= E (root G) (freeze p):=by
  conv_lhs=> arg 2; rw [← gone p];
  unfold scalar; rw [pit, show numbers (G:=G) (0: Scale.Tape G.Color)=0 from funext fun i=>by simp [numbers]]; rfl
structure Fee (G:Gauge) where
  k : ℕ
  line : Line G
  due : line ∈ cane k G
def Fee.cost (f:Fee G):ℕ:= 1+f.k
abbrev Word (G:Gauge) := List (Fee G)
def debt (p:Word G):= (p.map Fee.cost).sum
def story (L:Word G): Stamp G :=(L.map fun f=>harp f.line).prod
@[simp] lemma steam :story (G:=G) []=1:=rfl
lemma read_word (p:Word G)(f:Fee G): story (f::p)= harp f.line*story p:=rfl

def Keen (v:Line G→Prop)(n:ℕ) : Submodule ℂ (Stamp G):= Submodule.span ℂ (story '' {L:Word G| debt L=n∧∀ i∈L,v i.line})
abbrev OnStage (G:Gauge)(n:ℕ):=Keen (G:=G) Stops n
abbrev elemental (G:Gauge)(n:ℕ):=Keen (G:=G) (fun _=>True) n
lemma read_hard (h:Line G→Prop)(L:Word G)(H:∀ i∈L,h i.line):story L∈Keen h (debt L):= Submodule.subset_span ⟨L,⟨rfl,H⟩,rfl⟩
lemma good_read (h:Line G→Prop)(d:ℕ): Keen h d≤ elemental G d:=Submodule.span_mono (Set.image_mono fun _ hi=> ⟨hi.1,fun _ _=> trivial⟩)
lemma one_go (h:Line G→Prop):(1:Stamp G)∈ Keen h 0:=by simpa [debt] using read_hard h [] (by simp)
lemma read_cut (h:Line G→Prop)(L:Fee G)(p: h L.line): harp L.line ∈ Keen h L.cost:=by simpa [read_word,debt,story] using read_hard h [L] (by simpa using p)

abbrev Tile (G:Gauge):= Cover → Stamp G
inductive Book (G:Gauge) : ℕ→ Tile G→ Prop where
| zero n : Book G n 0
| unit : Book G 0 1
| left (x:Fee G): Book G x.cost (fun _=>harp x.line)
| right (x:Fee G): Book G x.cost (fun y=>harp (displace y x.line))
| rent (x y:Fee G): Book G (x.cost+y.cost) (fun p=> C ((↑(handshake (displace p y.line) x.line)):ℂ))
| mul {p q a b} : Book G a p→Book G b q→Book G (a+b) (p*q)
| add {p q a}: Book G a p→ Book G a q→ Book G a (p+q)
| scale {p a}: Book G a p→∀ c:ℂ,Book G a (c • p)

def books (G:Gauge)(n:ℕ): Submodule ℂ (Tile G) where
  carrier := {x|Book G n x}
  zero_mem':= Book.zero _
  add_mem' p q:= Book.add p q
  smul_mem' c _ p:= Book.scale p c

end YM.XSpace.Mu
