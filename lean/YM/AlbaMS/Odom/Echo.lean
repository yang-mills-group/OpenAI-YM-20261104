import YM.AlbaMS.Odom.Beam

/-!
# quotient owned coordinates

Any involution. Lattice period n is even for application. At the sixteen fixed
cells only one copy; important not using ghost volume twice there. We can delete
any based ghost point. No quotient by proof equality used in Ops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Odom
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Inlay Inlay.Net Lattice
variable {X R : Type*}{n : Side}{G:Gauge}

structure Token (X : Type*) where
 σ : X→X
 invol : Involutive σ
namespace Token
variable (S:Token X)
-- use arbitrary choice, stable at all sizes for that S
def orb (x:X):Set X:={x,S.σ x}
lemma isOrb (x:X): (S.orb x).Nonempty:=⟨x,by simp [orb]⟩
def chief (x:X):= (S.isOrb x).choose
lemma inside (x:X): chief S x∈ S.orb x:= (S.isOrb x).choose_spec
lemma split (x:X): chief S x=x ∨ chief S x=S.σ x:= by simpa [orb] using S.inside x
lemma share (x:X): chief S (S.σ x)= chief S x:=by unfold chief; congr! 1; ext y; simp [orb,S.invol x,or_comm]
lemma loyal (x:X): chief S (chief S x)= chief S x:= by
  rcases S.split x with h|h; rw [h,h]; nth_rw 1 [h]; rw [S.share]
abbrev Qual (S: Token X): Type _ := {x:X//S.chief x=x}
variable {S} in
instance [Fintype X]: Fintype (Qual S):= Subtype.fintype _
def pick (x:X): S.Qual:=⟨S.chief x,S.loyal x⟩
lemma picked (x:S.Qual): pick S x=x:= Subtype.ext x.property
lemma pick_σ (x:X): pick S (S.σ x)= pick S x:= Subtype.ext (S.share x)
lemma pick_eq (x y:X): pick S x=pick S y ↔ x=y ∨ x=S.σ y:=by
  constructor
  · intro h; have h: chief S x=chief S y:=Subtype.ext_iff.mp h; rcases S.split x with h1|h1 <;> rcases S.split y with h2|h2 <;> rw [h1,h2] at h
    exact Or.inl h; exact Or.inr h; exact Or.inr (S.invol x ▸ congr_arg S.σ h); exact Or.inl (S.invol.injective h) -- ordering
  rintro (rfl|rfl); rfl; exact S.pick_σ _
def extra (x:X):ℕ:= if S.σ x=x then 1 else 2
def NoPoint (S : Token X):Prop:=∀ x,S.σ x≠x
variable [Fintype X]
lemma sum_groups [AddCommMonoid R] (f:S.Qual→R) : (∑ x:X, f (pick S x))=∑ x:S.Qual, (S.extra x.val) • f x:=by
  have he x : f (pick S x)=∑ y:S.Qual,if pick S x=y then f y else 0:=by simp
  simp_rw [he]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _=>?_ ;
  have ht (x) : pick S x=y ↔ x=y.val ∨ x=S.σ y.val:=by nth_rw 1 [← S.picked y]; exact S.pick_eq ..
  by_cases h:S.σ y.val=y.val; · simp_rw [ht,h,or_self]; simp [extra,h]
  have hp (x:X): ite (pick S x=y) (f y) 0=(if x=y.val then f y else 0)+(if x=S.σ y.val then f y else 0):= by by_cases he:x=y.val<;>by_cases hv:x=S.σ y.val<;>simp [ht,he,hv,h,Ne.symm h]
  simp_rw [hp,Finset.sum_add_distrib]; simp [extra,h,two_smul]
end Token

def silver (n:Side) : Token (Site n):=⟨Neg.neg,neg_neg⟩
def copper (n:Side) : Token (Edge (Site n)) where
 σ e:= (-e.1-step e.2,e.2)
 invol e:=by show (-(-e.1-step e.2)-step e.2,e.2)=_; simp
lemma cop_nofix (h: Even n.val): (copper n).NoPoint:=by
  intro x hx; have he : (-x.1-step x.2 : Site n) x.2=x.1 x.2 := congr_fun (congr_arg Prod.fst hx) x.2; simp only [Pi.sub_apply,Pi.neg_apply, step_apply,if_true] at he
  let B := ZMod.castHom (R:=ZMod 2) (even_iff_two_dvd.mp h); have hh := congr_arg B he; simp only [map_sub,map_neg,map_one] at hh; generalize B (x.1 x.2)=v at hh; revert hh; fin_cases v <;> decide
abbrev Foil (n:Side) := (copper n).Qual
abbrev Angle (n:Side) := (silver n).Qual

def selects (b:Bool)(x:Angle n):Prop:= b=false ∨ x.val≠0
abbrev Nail (n:Side)(b:Bool):= {x:Angle n// selects b x}
instance mail (b:Bool): Fintype (Nail n b):= Subtype.fintype _ -- global maybe conflict

def recede (b:Bool)(x:Angle n):Option (Nail n b):= if h:selects b x then some ⟨x,h⟩ else none
def slur (b:Bool)(x:Site n) := recede b ((silver n).pick x)
lemma slur_neg (b:Bool) (x:Site n): slur b (-x)=slur b x:=by unfold slur; rw [show (silver n).pick (-x)= _ from (silver n).pick_σ x]
lemma slur_hp (b:Bool)(x:Nail n b): slur b x.1.1=some x:=by rw [slur,Token.picked,recede,dif_pos x.2]

def blush (n:Side)(b:Bool): Net (Foil n) (Nail n b) where
 head x:= slur b x.val.1
 foot x:= slur b (x.val.1+step x.val.2)

variable (n) (G) (b:Bool)
def typeFlip (x:Edge (Site n)): Bool:= decide ((copper n).chief x≠x)
def walkT : Receipt G (deck n) (blush n b) where
 parcel := (copper n).pick
 node := slur b
 flip := typeFlip n
 color:=1
 rate x:= if -x=x then 2 else 1
 start e:=by change slur b e.1= ite (typeFlip n e=true) _ _; simp only [blush, Token.pick,typeFlip,decide_eq_true_eq]; split_ifs with he; next=> rw [(Token.split (copper n) e).resolve_left he]; simp [copper,slur_neg] -- cases reconfig
             next=>rw [not_not.mp he]
 stop e:=by simp only [blush,Token.pick,typeFlip,decide_eq_true_eq]; split_ifs with he; next=> rw [(Token.split (copper n) e).resolve_left he]; change slur b (e.1+step e.2)= slur b (-e.1-step e.2); rw [show -e.1-step e.2= -(e.1+step e.2) by abel, slur_neg]
            next=> rw [not_not.mp he]; rfl
end YM.MSBar.Odom
