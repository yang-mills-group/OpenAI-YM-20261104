import YM.FVA2.Generator.Centering
/-!
# Expose the marked-slot calculus in the physical oriented-curvature representation

Generation grade m=taylor+2, no conditions lost on exchanging between $Even/H/Maxwell$.
Strengthen Sonar's regrouping of the complete Survey/edit line using the exact Curled
powers. For one vertex we can organize expansions in its three slots against ANY length of marked slots. Each attached-slot derivative retains one less
capacity through it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Pages
open Function Set XSpace Center XSpace.Mu XSpace.Trace XSpace.Chart2 MvPolynomial Lattice Next.Rank.Normal
open scoped Classical Topology BigOperators
variable {G:Gauge}{d e:ℕ}
structure Addr (G:Gauge) where
    y : Cover
    i : Axis
    j : Axis
    L : List Axis
    c : G.ColorIndex

def Addr.fee (γ:Addr G): Fee G:= ⟨γ.L.length+1, Trace.touch γ.y γ.i γ.j γ.L γ.c, touch_cane _ _ _ _ _⟩
def Addr.cost (γ: Addr G):= γ.fee.cost
lemma price (γ:Addr G): γ.cost=γ.L.length+2:=by unfold Addr.cost Addr.fee Fee.cost; dsimp only; omega
abbrev MultiplierEstimates (G:Gauge):= List (Addr G)
def ink (p:MultiplierEstimates G):= story (p.map Addr.fee)
def wage (p:MultiplierEstimates G):= debt (p.map Addr.fee)
@[simp] lemma wages (v:Addr G)(p:MultiplierEstimates G): wage (v::p)=v.cost+wage p:=rfl
@[simp] lemma inks (v:Addr G)(p: MultiplierEstimates G): ink (v::p)= harp v.fee.line * ink p:=rfl

def Library (G:Gauge)(d:ℕ):= Submodule.span ℂ (ink '' { p : MultiplierEstimates G|wage p=d })
lemma instock (p:MultiplierEstimates G): ink p ∈ Library G (wage p):=Submodule.subset_span ⟨p,rfl,rfl⟩
lemma title (p:MultiplierEstimates G): ink p∈ elemental G (wage p):= read_hard _ _ (fun _ _=>trivial)
lemma add_stock (p q:Stamp G)(hp:p∈ Library G d)(hq:q∈ Library G e): p*q∈ Library G (d+e):= by
    have hi : Library G d*Library G e≤Library G (d+e):= by rw [Library,Library,Submodule.span_mul_span]; apply Submodule.span_le.mpr; rintro t ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩; dsimp only; rw [ show ink u*ink v=ink (u++v) from by simp [ink,story] ]; refine ( show wage (u++v)=d+e from ?_ ) ▸ instock (u++v); rw [←show wage u=d from hu,←show wage v=e from hv]; simp [wage,debt]
    exact hi (Submodule.mul_mem_mul hp hq)
-- Strengthen Sonar.germ_hit & `allows` by the spin/grade card. `Degree` label is
-- supplied Curled finite-window reader, not a selection by any resonance test here.
open RG Wilson Labels Source Source.Drops
open XSpace.Scale XSpace.Litter XSpace.Sail Further.FreeCovariance.KP Next.Rank CellsInt Beamer
variable {H:Hol G} (S:Survey G H d)
private lemma bill (A:Contact G)(p:Degree G): Beamer.gesture p (input A)=probe (Trace.touch p.point p.a.val.1 p.a.val.2 (List.ofFn p.layout) p.paint) A:=by
    have he (l:ℕ)(t:Fin l→Axis)(P:Cover→G.Color): jumps l t P=crack (List.ofFn t) P:=by induction l generalizing P with | zero=> rw [List.ofFn_zero];rfl | succ l ih=>rw [jumps,List.ofFn_succ,Litter.snack]; exact ih (Fin.tail t) (Δf (t 0) P)
    rw [gesture_hits,shuttered,he,Trace.paid]
private lemma grip (γ:Addr G): harp γ.fee.line∈ Library G γ.cost:=by
    obtain he:= instock [γ]; rwa [inks,wages,show wage (G:=G) []=0 from rfl,show ink (G:=G) []=1 from rfl,Nat.add_zero, mul_one] at he
lemma booked (v:Labels.Key G): harp (headlines S v).line∈ Library G (generation v):=by
    change harp (ping S v) ∈ _
    by_cases h : generation v≤ d; swap; · rw [show ping S v=0 from inquire (by ext1 A; rw [ping_at,Cross.unused S v (not_le.mp h),map_zero];rfl),harp,map_zero,map_zero]; exact (Library ..).zero_mem
    obtain ⟨r,K,T⟩ := Cross.removes _ (Cross.blossoms S (Survey.component v)) (Cross.startsKey S v h); let g (i:Cross.Reading G v.1 r) : Addr G:= let p:=Cross.mood i; ⟨p.point,p.a.val.1,p.a.val.2,List.ofFn p.layout,p.paint⟩
    have he: harp (ping S v)=∑ i,(↑(K i):ℂ) • harp (g i).fee.line:=by
       apply Chart2.same; intro A; rw [leg_test,ping_at,show Cross.readKey S v _=_ from T (input A) (signal_s A), map_sum, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul, leg_test,bill]; exact Complex.ofReal_mul ..
    rw [he]; apply Submodule.sum_mem; intro i _; refine Submodule.smul_mem _ _ ((show (g i).cost=generation v from ?_) ▸ grip (g i)); rw [price,List.length_ofFn]; rfl
lemma resides (u:Labels.Key G →₀ℕ)(c:ℂ): Encore.reel S 0 (monomial u c)∈ Library G (Finsupp.weight generation u):=by
    apply Extra.FD.per_factor u; rw [map_zero,show monomial (σ:=Labels.Key G) 0 c=C c from rfl,← mul_one (C c),C_mul',map_smul,map_one]; exact Submodule.smul_mem _ _ (instock (G:=G) [])
    intro j k h; rw [monomial_add_single,pow_one,map_add,Finsupp.weight_single,one_smul,map_mul,reel_x]; exact add_stock _ _ h (booked S k)
lemma onfile (v:Labels.Pol G)(h:IsWeightedHomogeneous generation v e) : Encore.reel S 0 v∈ Library G e:= by rw [v.as_sum,map_sum]; refine Submodule.sum_mem _ fun j hj=>?_ ; rw [← h (MvPolynomial.mem_support_iff.mp hj)]; exact resides S _ _
lemma marked (p:On.Grade G d): Prelude.enter0 S p∈ Library G d:= onfile S _ (Price.natural p)
-- list derivative law; expose the ledger of slots removed at the mark under each
-- specified slot of the INTEGRATED cubic V3. (so A/B/C rows later straightforward).

def slip : MultiplierEstimates G → List (Addr G × MultiplierEstimates G)
| []=>[] | k::p=> (k,p)::(slip p).map (fun i=>(i.1,k::i.2))
lemma accounted {p:MultiplierEstimates G} {q: Addr G× MultiplierEstimates G}(h:q∈slip p) : q.1.cost+wage q.2=wage p:=by induction p generalizing q with
    | nil=> simp [slip] at h
    | cons k p ih=> rw [slip,List.mem_cons, List.mem_map] at h; rcases h with h|⟨u,h,rfl⟩; exact h ▸ rfl; have he:= ih h; simp only [wages]; omega
-- Tiles for the pieces in detachment
abbrev left (γ: MultiplierEstimates G) : Tile G:= fun _=> ink γ
abbrev right (γ:Bond G) : Tile G:= fun x=> harp (displace x γ.fee.line)
-- Use colorized cast of the *exact* lattice rent, no onset asymptotic here
abbrev gem (q:Addr G)(v: Bond G) : Tile G:= fun x=>C (↑(handshake (displace x v.fee.line) q.fee.line):ℂ)
abbrev binder (p: MultiplierEstimates G)(v:List (Bond G)) : Tile G:= bounces G (ink p) (story (v.map Bond.fee))
private lemma releaseD (p:MultiplierEstimates G)(v:Bond G)(x:Cover): Chart2.D (bake (displace x v.fee.line)) (ink p)= ((slip p).map (fun i=>(↑(handshake (displace x v.fee.line) i.1.fee.line):ℂ) • ink i.2)).sum:= by
    induction p with
    | nil=>rw [show ink (G:=G) []=1 from rfl]; simp [slip]
    | cons k p ih=> set t:=displace x v.fee.line; rw [slip,List.map_cons,List.sum_cons, inks, (D _).leibniz,played,ih]; change _ + _ * C (↑(handshake k.fee.line t):ℂ)=_; simp only [smul_eq_mul,List.map_map,Function.comp_def,inks]; rw [listening,mul_comm (ink p), C_mul',add_comm]; congr 1; rw [ ← List.sum_map_mul_left ]; simp

lemma freight (p:MultiplierEstimates G)(v:List (Bond G))(k:Bond G): binder p (k::v)= right k * binder p v + ((slip p).map (fun i=> gem i.1 k * binder i.2 v)).sum:=by
    funext x; rw [Pi.add_apply, Pi.mul_apply]; unfold binder bounces; rw [List.map_cons,read_word,map_mul,rings, Mu.flip,cross_rule,releaseD,map_list_sum,Mu.flip]; congr 1
    rw [List.map_map, show ∀ {ι:Type}(L:List ι)(z:ι→ Tile G), ((L.map z).sum) x= ((L.map (fun i=> z i x)).sum) from ?_ ]; congr 1; apply congr_arg (fun g: Addr G× MultiplierEstimates G→ Mu.Stamp G=> (slip p).map g); funext i; rw [Function.comp_apply,map_smul,Mu.flip, ← C_mul']; rfl
    intro i L z; induction L with | nil=>rfl | cons i w ih=>simp only [List.map_cons,List.sum_cons,Pi.add_apply,ih]
@[simp] lemma closed (p:MultiplierEstimates G): binder p []=left p:=funext fun x=>by unfold binder bounces; rw [List.map_nil, Mu.steam,map_one,tie_one]
end YM.FVA2.Generator.Pages
