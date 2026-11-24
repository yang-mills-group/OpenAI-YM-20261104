import YM.RegulatorIR.Gain.Vault

/-!
# Pricing $\Phi$ on sites
Root convention: start and signed. Need even diagonal at orientation summation.
Fixed sites allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{I J X Y:Type}{f c:Side}{P l u:ℝ}

-- Motion-induced translations f and c coherent as before. $\phi$ even result, take minus sign in generating transformation legs.
abbrev Point (G: Gauge):= Cover×G.ColorIndex
abbrev OPoint (G:Gauge)(f:Side):= Site f×G.ColorIndex
abbrev Bride (G:Gauge):=Layer (Point G) (Foot G)
def roam (f:Side) (d:Motion)(x:Cover):Cover:= match d with
 | .across v=> x+f.val • v
 | .turn v=> -x+f.val • v
lemma roam_x (n:Side) (d:Motion)(u:ℝ)(x:Cover): Motion.slide u (roam n d x)= Motion.loc (u*n.val) d (Motion.slide u x):=by cases d <;> simp only [roam,map_add,Geometry.turns_site,map_neg] <;> unfold Motion.loc <;> rw [add_comm]
lemma gramE {x y:Cover}(he:wrap f x=wrap f y):∃ g:Cover, x=roam f (.across g) y:=by
 obtain ⟨v,h,-⟩:= channel_eq f (y,(0:Axis)) (x,0) (Prod.ext he.symm rfl); refine ⟨v,Eq.trans (congr_arg Prod.fst h) ?_⟩; exact add_comm ..

def Rune (A:Deck P (Foot G) X)(f:Side)(V:Bride G):Prop:=∀ v x y i,V (roam f v x,i) (A.wind v y)=v.sign* V (x,i) y

def dyes (F:Bride G)(A:Deck P (Foot G) X)(x:Point G)(v:Foot G):= F x v*A.orient v
def roundS (F:Bride G)(A:Deck P (Foot G) X)(x: Point G)(v:X):= Stalk.collect A.orbit (dyes F A x) v
def scene (F:Bride G)(A:Deck P (Foot G) X)(x: OPoint G f):= roundS F A (Lattice.lift x.1,x.2)
variable {A:Deck P (Foot G) X}{V:Bride G}
lemma preserve (d:Motion)(x:Cover)(i:G.ColorIndex)(t)(H:Rune A f V): roundS V A (roam f d x,i) t=roundS V A (x,i) t:=by
 let E: Equiv.Perm (Stalk A.orbit t):= Equiv.subtypeEquiv (A.wind d) (fun a:Foot G=> show A.orbit a=t ↔ _ from by rw [A.projected]);
 unfold roundS Stalk.collect; rw [← E.tsum_eq]; apply tsum_congr;intro a; unfold dyes;change V _ (A.wind d a.val)*A.orient (A.wind d _)= _; rw [A.retreat,H,mul_mul_mul_comm,Motion.sign_sq,one_mul]
lemma rises (H:Rune A f V)(x:Cover)(i:G.ColorIndex) : scene V A (wrap f x,i)=roundS V A (x,i):=by
 unfold scene; dsimp only; let y:=wrap f x;obtain ⟨v,hv⟩:= gramE (wrap_lift y);change roundS V A (Lattice.lift y,i)= _;rw [hv]; ext1 b; exact preserve (.across v) _ _ _ H
lemma moonlit (H:Rune A f V)(x:Site f)(i) : scene V A (-x,i)=scene V A (x,i):=by
 obtain ⟨v,rfl⟩ : ∃ v:Cover,wrap f v=x:=⟨_,wrap_lift x⟩; rw [← map_neg, rises H, rises H]; ext1 p
 rw [show -v=roam f (Motion.turn 0) v from (by simp [roam])]; exact preserve _ _ _ _ H
-- Path matrix

def valve (F:Layer (Foot G) (Foot G))(V:Bride G)(x:Foot G)(y:Foot G) := F x y+(V (x.1.1,x.2) y - V (x.1.1+Lattice.step x.1.2,x.2) y)

variable {F D:Layer (Foot G) (Foot G)} (hS: Even f.val)(hℓ:l*f.val=P)
local notation "E" => Carto G l P hS hℓ
lemma ferry (H:Rune A f V)(hs:Billed F)(hc:Billed V)(ht:D=valve F V)(i: Book G f)(x:X) : fmat E A D i x= fmat E A F i x + (scene V A (i.1.val.1,i.2) x-scene V A (i.1.val.1+Lattice.step i.1.val.2,i.2) x):=by
 let p:= (E).place i; let y:= (p.1.1,i.2);let z:Point G:= (p.1.1+step p.1.2,i.2);let V':=scene V A (f:=f)
 have h₁: V' (i.1.val.1,i.2)= roundS V A y:=rfl
 have h₂: V' (i.1.val.1+step i.1.val.2,i.2)= roundS V A z:=by
    have hp: wrap f z.1=i.1.val.1+step i.1.val.2:=by unfold z; dsimp only; rw [map_add,wrap_step]; change wrap _ (Lattice.lift _)+ _=_; rw [wrap_lift];rfl
    rw [← hp]; exact rises H z.1 i.2
 unfold V' at h₁ h₂; rw [ht,h₁,h₂]
 have hp (u:Point G): Summable (fun v:Stalk A.orbit x=> dyes V A u v.val):=by
    apply Summable.comp_injective (f:=dyes V A u) _ Subtype.val_injective; apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_eq _ (V u) 1 (fun i=>by unfold dyes;rw [enorm_mul,A.over_sign,mul_one])]; exact hc.rows u
 let g:= fun v:Stalk A.orbit x => paint E A F p v.val
 have hx :Summable g:= (hs.paints ..).comp_injective Subtype.val_injective
 change (∑' V:Stalk A.orbit x, _)= (∑'v,g v)+ ((∑' v:Stalk A.orbit x, dyes V A y v.val)-∑' v:Stalk A.orbit x,dyes V A z v.val)
 rw [← (hp y).tsum_sub (hp z),← hx.tsum_add ((hp y).sub (hp z))]; apply tsum_congr;intro v; simp only [paint,valve,(E).north,one_mul,g]; unfold dyes; change (_ + (V y v.val-V z v.val))*A.orient v.val= _; rw [show (E).orient p=1 from Deck.north ..]; unfold p;ring

section Loom
variable (F:Layer (Foot G) X)(V0 :Layer (Point G) X)

def tubeL (e:Edge Cover)(j: Mood G):= (![F (e,j.2),V0 (e.1,j.2),V0 (e.1+Lattice.step e.2,j.2)]:Fin 3→ X→ℝ) j.1
end Loom

section Cost
variable (p:ℕ) {c:ℝ≥0∞}{μ:ℝ} (hm:0<μ)(hP:0<P)
local notation "F1" => Tariff.native μ hm p
local notation "G1" => Tariff.onFold P hP μ hm p
-- scene post markup. Data row target T. Same X. pos site physical native.

def pointS (l:ℝ)(p:Point G): Room:=Motion.slide l p.1
def pointO (l:ℝ) (p:OPoint G f):Room:=pointS l ((Lattice.lift p.1,p.2):Point G)
lemma hike (V:Bride G)(A:Deck P (Foot G) X)(h:row V F1 (pointS l) A.pos c) :row (scene V A) G1 (pointO (G:=G) (f:=f) l) A.atO c:=by
 intro i
 let x:Point G:= (Lattice.lift i.1,i.2);let f:= dyes V A x
 apply le_trans (Stalk.quota_collect A.orbit f _)
 rw [quota_eq _ (V x) _ (fun i=>by unfold f dyes; rw [enorm_mul,A.over_sign,mul_one])]
 apply (quota_mono (V x) ?_).trans (h x)
 intro i; dsimp only [Function.comp_apply]
 apply Tariff.amount_mono hm
 rw [A.x_tile hP]; exact (Spatial.distance_le hP _ _ (.across 0)).trans_eq (by rw [neutral_loc];rfl)
end Cost
end YM.RegulatorIR.Gain
