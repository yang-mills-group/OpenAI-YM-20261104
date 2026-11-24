import YM.MS.City.Dye
/-!
# Conjugation-real on all length symbols

Use conjugate periodic not Hermitian field order reverse. Ghost charge-int rails
 ensures kernel parity needed for cross. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color
open Native.Paint Detect
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H:Landau.Detect.Law G} {K: Flux (BH G) QP ℂ}{b:Bool}{d d':ℤ}{t:ℝ}
private instance : Measure.IsNegInvariant μzone:= capN

def World (F:Law G): Prop:= ∀ w, F (invertMom w)=star (F w)
abbrev RealF (K:Flux (BH G) QP ℂ): Prop:= ∀ i j x,K i j (-x)=star (K i j x)
lemma truthP : RealF (Cpu G t):= by
    intro i j x; unfold Cpu LegsK Landau.choir; split;
    · rw [wave_neg]; rcases i with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|b,_|_⟩,j⟩ <;> first| (solve| simp only [L0,star_zero]) | simp [L0,brush_neg]
    rw [star_zero]
lemma inv_trc (h:World F)(hk:RealF K)(q:QP)(l): trc K (-q) F (invertMom l)=star (trc K q F l):= by
    simp_rw [at_trc,hk,star_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun j _=>?_); rw [star_mul']; exact congr_arg _ (h ((i,q)::(j,-q)::l))
lemma inv_trace (h:World F)(hk: RealF K): World (Ccy K F μzone):= by
    intro l; unfold Ccy; rw [← integral_neg_eq_self (μ:=μzone) (fun q=>trc K q F (invertMom l))]; simp_rw [inv_trc h hk]; exact integral_conj -- available
lemma wait_cross {b c:Bool}: star (Koszul.cross b c:ℂ)= cross b c:= by cases b <;> cases c <;> simp
lemma scatter_C (u:List (Lane4 G))(F:Shared (Lane4 G) ℂ) : star (scatter (field parity) u F)=scatter (field parity) u (fun a b=>star (F a b)):= by
    induction u generalizing F with
    | nil=>rfl
    | cons i l ih=> rw [scatter_cons,ih,scatter_cons]; simp_rw [star_add,star_mul',wait_cross]
lemma ps_inv (v:List (Lane4 G)): degree (field parity) (invertMom v)=degree (field parity) v:= by induction v with| nil=>rfl| cons i v ih=> rw [show invertMom (i::v)=(i.1,-i.2)::invertMom v from rfl, degree_cons,degree_cons,ih] 
lemma globe (hf:World F)(hg:World H)(hk:RealF K)(hr:Reverse K parity): World (tree parity K F H):= by
    intro l; unfold tree; rw [scatter_C, invertMom,Lifting.scatter_move _ (fun i:Lane4 G=> (i.1,-i.2)) (fun _=>rfl)]; apply scatter_congr; intro a b _; change attaches _ _ _ _ (invertMom a) (invertMom b)=_; simp_rw [convertR hr,star_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun j _=>?_); unfold radius; dsimp only
    rw [net_invert,ps_inv,hk i j (-net a), show - - -net a= - (- -net a) from rfl,show F ((i,- -net a)::invertMom a)= _ from hf ((i,-net a)::a), show H ((j,- - -net a)::invertMom b)= _ from hg ((j,- -net a)::b)]; simp only [star_mul',wait_cross,star_ofNat]
-- rail
def wins (F:Law G)(v:ℤ): Prop:= Rails (ghostNo ∘ Prod.fst) v F
lemma chargeF (w:List (Lane4 G)): Koszul.chargeInt (ghostNo ∘ Prod.fst) w=fieldDim ghostNo w:=rfl  -- List map
lemma l_zero {i j:BH G} {q:QP}(h:Cpu G t i j q≠0): ghostNo i+ghostNo j=0:= by
    contrapose! h; unfold Cpu LegsK Landau.choir; split; swap; rfl
    rcases i with ⟨⟨_|_,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|_,_|_⟩,j⟩ <;> norm_num [ghostNo,ghostChannel] at h <;> rfl
lemma winsL (h:wins F d) (ht:∀ i j q,K i j q≠0→ ghostNo i+ghostNo j=0): wins (Ccy K F μzone) d:= by
    intro l he; unfold Ccy; have hz (q:QP) : trc K q F l=0:= by rw [at_trc]; refine Finset.sum_eq_zero (fun i _=> Finset.sum_eq_zero (fun j _=>?_)); by_cases hh:K i j q=0; rw [hh,zero_mul]; rw [h ((i,q)::(j,-q)::l) ?_,mul_zero]; rw [chargeF] at he ⊢; simp only [field_cons]; rw [← add_assoc,ht i j q hh,zero_add]; exact he
    simp_rw [hz]; simp
lemma win_tree (h:wins F d)(hh:wins H d')(hr:Reverse K parity)(ht:∀ i j q,K i j q≠0→ ghostNo i+ghostNo j=0): wins (tree parity K F H) (d+d'):= by
    intro l hl; rw [tree,scatter_congr _ l _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..)
    intro a b he; rw [convertR hr]; refine Finset.sum_eq_zero (fun i _=> Finset.sum_eq_zero (fun j _=>?_)); unfold radius; dsimp only; by_cases hv: K i j (-net a)=0; rw [hv]; ring; obtain hg:= ht i j _ hv; let Z l:=fieldDim (ghostNo (G:=G) (D:=Axis)) (l:List (Lane4 G));
    by_cases hx:ghostNo i+Z a=d; swap; · rw [h ((i,-net a)::a) (by rw [chargeF,field_cons]; exact hx)]; ring
    have H : ghostNo j+Z b≠d':= by rw [chargeF] at hl; intro H; have hv : Z a+Z b=Z l:= split_sum (ghostNo ∘ Prod.fst) he; replace hl:Z l≠d+d':=hl; omega
    rw [hh _ (show _ from ?_),mul_zero]; rw [chargeF,field_cons]; exact H -- dependency
end YM.MS.City
