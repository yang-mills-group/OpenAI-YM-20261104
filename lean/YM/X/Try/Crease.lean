import YM.X.Try.Hub
import YM.X.Bare.Marks
/-! # Choosing grade-2 curvature channels. natural at all horizons. valuation rank trans. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal LiftMark Configuration MvPolynomial Function Filter Set Asymptotics Gauge
open Source Drops PertExtension LatticePT Gauge ProjectorNext.Calibration Maxwell Bid Hue Grow Clove Dial Next.Foundations Labels Spindle Pert.RawLabels Extra.FD
open Stems hiding X
open Heat.Top hiding test
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d n k:ℕ} {V I:Type*}
local notation "L₀"=> Taylor G 0
local notation "Pθ"=> poly (CoverC G)
local notation "Ξ"=> CoverC G
def basis_eval (x:CoverC G): Module.Dual ℝ L₀ where
    toFun P:= curτ P x.1 x.2
    map_add' p q:= by have h:= congr_arg Subtype.val ((Maxwell.potential (G:=G)).map_add p q); change takeCurl (p+q) _ _ _ _=_; change takeCurl (p+q) =_ at h; rw [h]; rfl
    map_smul' r p:= by have h:=congr_arg Subtype.val ((Maxwell.potential (G:=G)).map_smul r p); change takeCurl (r•p) _ _ _ _= _; change takeCurl (r • p)=_ at h; rw [h]; rfl
-- polynomial marker via ColorMap
abbrev token (G:Gauge):= (Key G)
local notation "Λ"=> token G
def approx (x:CoverC G): (Key G)→₀ℂ:= ∑ j:Fin (Labels.dim G 0), (↑(basis_eval x (axes G 0 j)):ℂ) • Finsupp.single (⟨0,j⟩:Λ) 1
def cleanDial (G:Gauge):  (poly (CoverC G)) →ₐ[ℂ] Pol G:= exchange approx
lemma apply_dial (X₀: Labels.Jet G)(p:Pθ): Labels.read X₀ (cleanDial G p)= peek (X₀ 0) p:= by
   apply DFunLike.congr_fun (f:=(Labels.read X₀).comp (cleanDial G)); ext1 i; rw [AlgHom.comp_apply,cleanDial,Normal.exchange_x,peek,Hue.display,aeval_X];
   let L:= basis_eval i; let U:= axes G 0; change Labels.read _ (Normal.glyph (approx i)) = (↑(L (X₀ 0)):ℂ); conv_rhs=> rw [← U.sum_repr (X₀ 0)]
   unfold approx; simp only [map_sum,map_smul, glyph, Finsupp.linearCombination_single, one_smul, Labels.read,aeval_X, Complex.ofReal_sum, smul_eq_mul,Complex.ofReal_mul]; apply Finset.sum_congr rfl; intro t _; rw [mul_comm]; rfl
lemma grade_dial_X (i:CoverC G): IsWeightedHomogeneous Labels.bidegree (cleanDial G (X i)) (2,1):= by
   rw [cleanDial,exchange_x]; unfold approx; rw [map_sum]; refine IsWeightedHomogeneous.sum _ _ _ ?_; intro j _; rw [map_smul,glyph,Finsupp.linearCombination_single,one_smul, ← C_mul']; exact (isWeightedHomogeneous_X ..).C_mul _
lemma grade_dial (p:Pθ)(h:HC p d): IsWeightedHomogeneous Labels.bidegree (cleanDial G p) (2*d,d):= by
   nth_rw 1 [p.as_sum]; rw [map_sum]; apply IsWeightedHomogeneous.sum; intro i hi; have hw: Finsupp.weight (fun _ : CoverC G=> ((2,1):ℕ×ℕ)) i=(2*d,d):= by rw [← show degree i=d from h (mem_support_iff.mp hi), Finsupp.weight_apply, Heat.Top.degree_eq,Finsupp.sum,Finsupp.sum]; ext; all_goals simp [Finset.mul_sum, Prod.fst_sum,Prod.snd_sum, mul_comm]
   rw [←hw]; exact Maxwell.Free.bounded_grade (fun _:CoverC G=>((2,1):ℕ×ℕ)) Labels.bidegree _ grade_dial_X i _ -- wrong arg
lemma freeze_dial (u:Labels.Taylor G 0): rebase G 0 u=u:= by
    let v:Shell G 0:= ⟨takeCurl u, Reed.coolZ _ (closedCurl u)⟩; have hx:u=gaugeJet v:= potential.injective (Subtype.ext (match_leg v).symm); unfold rebase; rw [hx,LinearMap.comp_apply, sends_back]
lemma color_dial (p:Pθ)(h:Hue.Fixed p): cleanDial G p ∈ invariantSpace G:= by
   intro v u; rw [apply_dial,apply_dial]; have he : curτ (Taylor.paint u (v 0))=Hue.tint u (curτ (v 0)):= by unfold curτ; rw [takeCurl_color]; rfl
   change peek _ p=peek _ p; rw [peek,show colored u v 0=Taylor.paint u (v 0) from rfl,he,h]
lemma limited_dial (hp:2*d≤n) (p:Pθ)(h:HC p d): cleanDial G p∈Labels.limited G n:= by
    apply (MvPolynomial.mem_restrictSupport_iff ℂ).2; intro i hi; change Labels.height i≤n; have ht:=grade_dial p h (MvPolynomial.mem_support_iff.mp hi); rw [weight_slot] at ht; exact congr_arg Prod.fst ht|>.trans_le hp
variable {p:Normal.poly (CoverC G)} (hp:2*d≤n)(h:HC p d)(hu:Hue.Fixed p)
def crease : Label G n:= ⟨cleanDial G p, limited_dial hp p h,color_dial p hu⟩
lemma creased : crease hp h hu ∈ Grade (2*d,d):= grade_dial p h
lemma continues : fixedPolynomial G n (crease hp h hu)=crease hp h hu:= by apply Subtype.ext; apply Labels.eval_ext; intro A; rw [show (fixedPolynomial G n (crease hp h hu)).val=changed (rebase G) (cleanDial G p) from rfl, eval_changed]; change Labels.read _ (cleanDial _ _)=Labels.read _ (cleanDial _ _); rw [apply_dial,apply_dial]; rw [show changedJet (rebase G) _ _= A 0 from freeze_dial (A 0)]
lemma keeper_dial (F:Frames G): physicalLabel F n (enroll F n (crease hp h hu))=crease hp h hu:= by rw [embed_round,continues]
-- reality
lemma real_crease (hb:Hue.Clear p): Labels.realBar (crease hp h hu)=crease hp h hu:= by
    refine Subtype.ext (Labels.eval_ext _ _ ?_); intro t; change Labels.read t (Labels.conjPol _) =_; rw [Labels.conj_value]; change star (Labels.read t (cleanDial _ _))=Labels.read t (cleanDial _ _); rw [apply_dial]; exact hb _
open Bare
variable (f : Labels.Frames G) (S:Bare.Shop f) (i:(f.level n).Index)
lemma mantra_axis (hd:0<d) (y:Label G n)(hc: y∈ Grade (2*d,d))(T:Taylor G 0) : peek T (common S (fun x=>mantra x d) n y)= Labels.read (chunk T) y.val:= by
   rw [← (f.level n).basis.sum_repr y,map_sum,map_sum,AddSubmonoidClass.coe_finsetSum, map_sum]; refine Finset.sum_congr rfl (fun i hi=> ?_); rw [map_smul,map_smul,Submodule.coe_smul_of_tower,map_smul]; by_cases hv:grade f i=(2*d,d); swap; · rw [show (f.level n).basis.repr y i=0 from (f.level n).power_coefficient i (Ne.symm hv) hc,zero_smul,zero_smul]
   rw [common_name]; apply congr_arg; rw [← base_weight_val S,peek_mark T _ ?_ (congr_arg Prod.fst hv) ?_]; · rw [use_weight,show wt f i=2*d from congr_arg Prod.fst hv]; omega
   exact congr_arg Prod.snd ((base_grade f i).trans hv) -- order
lemma known_price (hd:0<d): common S (fun x=>mantra x d) n (crease hp h hu)=p:= by
    refine peek_ext (fun T=>?_); rw [mantra_axis f S hd _ (creased hp h hu)];
    change Labels.read (chunk T) (cleanDial G p)=_; rw [apply_dial, chunk,Pi.single_eq_same]
-- no stanza
end YM.PositionX.Tri
