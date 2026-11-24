import YM.QuadraticLocal.Aperture.School
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Toggle
open Function Filter MeasureTheory Finset Lattice
open Topology AllOrder AllOrder.Fire AllOrder.Laplace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open Marker Multi Sunrise Drawer
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {V:Type}[DecidableEq V][Fintype V] {Y:Type}{k m n:ℕ}
local notation "T"=> V→Bool
local notation "I"=> V→ℝ
variable (V) in
abbrev Crew:= V→Bool
variable (s:V) (t:Crew V)
def ballot (x:Bool):ℝ:= if x then 1 else 0
def grant (x:Bool):ℝ:= if x then 1 else -1
abbrev convertS (i:V):ℝ:= Toggle.ballot (t i)
abbrev theta:=∏ i:V, grant (t i)
def flip (i:V):Bool:= if i=s then !(t i) else t i
def flop : Equiv (Crew V) (Crew V):= ⟨Toggle.flip s,Toggle.flip s,(fun u=> funext fun i=> by by_cases h:i=s<;> simp [Toggle.flip,h]),(fun u=> funext fun i=>by by_cases h:i=s<;> simp [Toggle.flip,h])⟩
lemma sound (w:Crew V): theta ((flop s) w) = - theta w := by
 let U:Finset V:= univ.erase s; let f:= (flop s) w; have he : grant (f s)= - grant (w s):= by change grant (Toggle.flip s w s)=_; unfold Toggle.flip; rw [if_pos rfl]; cases w s <;> simp [grant]
 let X(q:Crew V):=∏ i∈U,grant (q i); have ht(t:Crew V): theta t= grant (t s) * X t:= (Finset.mul_prod_erase _ _ (mem_univ s)).symm
 have hh : X f=X w:= Finset.prod_congr rfl fun i hi=> congr_arg grant (if_neg (mem_erase.mp hi).1)
 change theta f =_; rw [ht, ht,he,hh]; ring
lemma expected {W:Type} [CommMonoid W](f g:V→W)(L:Multiset V)(he:∀ i∈ L,f i=g i): (L.map f).prod=(L.map g).prod:= by
 congr 1; exact Multiset.map_congr rfl he
-- alternating Boolean estimator extracts the joint coefficient at total degree #types. Resonance.Charge.Static.
def alt (f:I→ℝ) :ℝ:=∑ v:Crew V, theta v * f (convertS v)
lemma opposite (P:Multiset V)(hs:s∉P): Toggle.alt (V:=V) (fun v:V→ℝ=> Drawer.view v P)=0:=by
 let f v:= theta v*view (convertS v) P; have he v: f (flop s v)= - f v:=by
    unfold f; have hS:view (convertS (flop s v)) P=view (convertS v) P:=expected _ _ P (fun i hi=>congr_arg Toggle.ballot (if_neg (show i≠s from fun h=> hs (h ▸ hi)))); rw [hS,sound]; ring
 have hz:= (flop s).sum_comp f; simp_rw [he,Finset.sum_neg_distrib] at hz; change ∑ w,f w=0; linarith
local notation "U"=> (Finset.univ:Finset V)
lemma beat (P:Multiset V)(hp:∀ i:V,i∈ P): Toggle.alt (V:=V) (fun v:V→ℝ=> Drawer.view v P)=1:=by
 let T':Crew V:= fun _=> true; unfold Toggle.alt; let v t:= view (V:=V) (convertS t) P
 rw [Finset.sum_eq_single_of_mem T' (by simp)]; · simp [T',theta,grant,Drawer.view,convertS,ballot]
 intro i _ hi; have he : ∃ x,i x=false:=by by_contra! h; exact hi (funext fun x=> by change _=true; cases h':i x <;> simp_all)
 obtain ⟨x,hx⟩:=he; have hx' : view (convertS i) P=0:= Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x,hp _,by simp [hx, convertS,ballot]⟩) -- arg
 exact (congr_arg (theta i*·) hx').trans (mul_zero _)
lemma sold (P:Multiset V)(h:P.card ≤ Fintype.card V)(he:∀ i:V,i∈P): P=(univ:Finset V).val:= (Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (Finset.nodup _)).mpr (fun ⦃i⦄ _=>he i)) h).symm
local notation "F"=> Sunrise.Focus.census V
local notation "X"=> Sunrise.Focus.pose
local notation "Q"=> Scatter.transmit F X
open Sunrise Sunrise.Focus
abbrev value (L:Multiset V): Poly (Sunrise.Focus.census V):= (L.map Sunrise.Focus.pose).prod
lemma geometry (P:Multiset V): Scatter.transmit (Sunrise.Focus.census V) (pose) (fun x:V→ℝ=> view x P) = (P.map pose).prod:=by
 induction P using Multiset.induction_on with
 | empty => exact Scatter.one _ _
 | cons i P ih=>
    let f (x:V→ℝ):= view x P; let w:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℝ) i; have ht:Plausible f:= (School.simpleR P).read
    rw [show (fun x:V→ℝ=> view x (i::ₘ P))=(w*f) from funext fun y=> by simp [w,f,Drawer.view],Scatter.carry (Rank.line w|>.read) ht, Multiset.map_cons,Multiset.prod_cons, show Scatter.transmit F (pose) w=pose i from Scatter.factor _]; exact congr_arg (pose i*·) ih
lemma vacant (P:Multiset V)(he:s∉P)(x:Finset V)(hx:s∈ x) : (value P).part (onto x)=0:=by
 induction P using Multiset.induction_on generalizing x with
 | empty => change (1: Poly F).part _=0; rw [Poly.one_part,if_neg (fun h: onto x=(F).quiet=>Finset.notMem_empty _ ((show x=∅ from congr_arg Subtype.val h) ▸ hx))]
 | cons i P ih=>
    have hp : s ≠ i ∧ s∉P:= by simpa using he
    rw [value, Multiset.map_cons, Multiset.prod_cons, Poly.part_mul]; refine sum_eq_zero fun i' _=> sum_eq_zero fun j hj=>?_ ; split
    next ht=>
      by_cases hh:i'=onto {i}
      · subst i'; let u:= j.val; have hz: s∈ u:= by
           have he:{i} ∪ u=x:=ht.2; rw [←he,Finset.mem_union] at hx; exact hx.resolve_left (fun h=> hp.1 (Finset.mem_singleton.mp h))
        change (pose i|>.part _) * (value P|>.part (onto u))=0; rw [ih hp.2 u hz,mul_zero]
      change ((Poly.send (onto {i}) 1).part _) * _=0; rw [Poly.part_send,if_neg hh,zero_mul]
    next=> rfl

lemma censusP (P:Multiset V)(h:P.card ≤ Fintype.card V): (value P).part (onto univ)= Complex.ofReal (Toggle.alt (fun v:V→ℝ=> Drawer.view v P)):= by
 by_cases hz: ∃ i:V,i∉P; · obtain ⟨s,hs⟩:=hz; rw [vacant s P hs U (mem_univ _),opposite s P hs]; rfl
 push Not at hz
 rw [beat P hz, sold P h hz]; change ((∏ i:V, pose i).part _)=_; rw [collects U,Poly.part_send]; simp
lemma alt_plus {f g:I→ℝ}: alt (f+g)=alt f+alt g:=by unfold alt; simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
lemma alt_times (v:ℝ) {f:I→ℝ}: alt (v • f)=v*alt f:=by unfold alt; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); simp only [Pi.smul_apply,smul_eq_mul]; ring
variable {C:Drawer Y}{u: (Drawer.Knife V)×Y→ℝ}
lemma handover (h:Drawer.School C k u)(x:Y)(hx:k ≤ Fintype.card V): (Scatter.transmit F pose (fun z:V→ℝ=>u (z,x))).part (onto univ)=Complex.ofReal (Toggle.alt (fun z:V→ℝ=>u (z,x))) :=by
 induction h with
 | one L h f hf=>
    let a(p:I):= Drawer.view p L; have he:(fun z:I=>shape L f (z,x))=(f x) • a:=funext fun i=> mul_comm _ _
    rw [he,Scatter.mul _ _ _ (School.simpleR _|>.read),Poly.part_smul,geometry L,censusP L (h.trans hx),alt_times,Complex.ofReal_mul]
 | @graft f g h₀ h₁ a b=>
    let u z:= f (z,x); let v z:= g (z,x)
    change (Scatter.transmit F pose (u+v)).part _= (alt (u+v):ℂ); rw [Scatter.sends (h₀.understands _) (h₁.understands _),Poly.part_plus,alt_plus,Complex.ofReal_add]; exact congr_arg₂ (·+·) a b
end YM.QuadraticLocal.Aperture.Toggle
