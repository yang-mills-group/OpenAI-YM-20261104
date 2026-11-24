import YM.OPE.Compatible.Atlas.Spine
/-! In free continuum for the complex comparator. With polynomial budgets still. Need downstream signed unions and Real transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V J:Type}[PartialOrder X][OrderBot X][Fintype X][Fintype J] (D:Origin X){Q:Finset X}
   {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U: Spec.Final C F S)
   {ψ:Filter V}{T: V→ℝ} {s: V→X→ℝ}
set_option quotPrecheck false
variable (A:Allot C)(h:Services C F S) (hL:Lanes (F:=F) U.sector.derivatives)
   {P:Prescription U.sector.derivatives} (hP:P.Coherent)
   (p:brim D Q→ C.book.Token) (r:V→Viewers U)(y: V→ J→E4)(q:J→ C.book.Token)
   (H: Burst D Q ψ T s){η M c:ℝ}(hη:0<η)
local notation "V'"=> fun i=>volume D Q (fun j=>(p j).1) (s i)
local notation "fuel"=> fun (d:ℕ) i=> V' i /(s i ⊥)^d
include H
lemma weighing (d:ℕ): ∀ᶠ i in ψ,0≤fuel d i ∧ fuel d i ≤ Real.exp ((d:ℝ)*T i):=by
   have ht:= H.fresh 1 one_pos; have he:= H.crown D
   filter_upwards [H.fronts, ht.brim_paid D p, ((ht.fade _ ht.crowned.base).mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one),time_bright D ht|>.lit] with i hf hh hs hp
   let a:=s i
   have hR:0<s i ⊥:=hp.pos _ he.base
   have hV: ∀ j: brim D Q, 0<a (par D j.val) ∧ a (par D j.val) ≤ 1:=by intro j; have hx:par D j.val∈Q:= (on_brim ..).mp j.2 |>.2.2; exact ⟨hp.pos _ hx,(hp.range' ⊥ _ bot_le hx).trans hs⟩ -- nested let
   have hv: V' i ≤ 1:= Finset.prod_le_one (fun j _=>pow_nonneg (hV j).1.le _) (fun j _=>pow_le_one₀ (hV j).1.le (hV j).2)
   refine ⟨div_nonneg hh.le (pow_nonneg hR.le _), (div_le_div₀ (by norm_num) hv (pow_pos (Real.exp_pos _) d) (pow_le_pow_left₀ (Real.exp_nonneg (-T i)) (hf _ he.base) _)).trans_eq ?_⟩; rw [Real.exp_neg, inv_pow,one_div,inv_inv,Real.exp_nat_mul]
lemma enhanced (g:ℕ) (m:X→ E4)(s : X→ℝ)(t:ℝ)(hr:Ridge s η M D Q m)(hx: Screened D Q C m (aperture D C 1 g η t s)): Address C D Q g 1 t s η M m:= ⟨hr, shutter_final D Q (H.crown D) m hx.angel, hx.stops⟩ -- `[V]` cannot infer H? transp hp
include A h hL hη hP
variable (hM:0 ≤ M)
include hM
lemma sturdy_coeff (w:Mode U.sector.derivatives): ∃ f:V→ℝ,Score ψ T f∧ ∀ᶠ i in ψ,∀ x:X→ E4,Ridge (s i) η M D Q x → ‖P.ope w (picked _ x) p 0‖ * V' i/(s i ⊥)^w.fst ≤f i:=by
    obtain ⟨l,hl⟩:=root_cast D H p P w (M:=M+1) (by positivity:0<η/2); obtain ⟨g,hg,he⟩:= pol_coeff (b:=1) U hP A D p (H.fresh (η/2) (by positivity)) hL h le_rfl (by positivity :0 ≤ M+1) 2 w
    obtain ⟨f,hf,hκ⟩:= Auth.encode (A:=l) D A h.simpleGate H (weighing D p H w.fst) hl (by norm_num) hη hg (B:=1) (he.mono fun i h x hx hv=> (show fuel w.fst i * _ ≤ _ from le_trans (le_of_eq (by ring)) (h x (enhanced D H 2 x _ _ hx hv)))) -- check U implicit
    refine ⟨f,hf,hκ.mono fun i h x hx=>?_⟩; refine le_trans (le_of_eq ?_) (h _ hx); ring
lemma sturdy_test (d:ℕ)(hc:0<c)(hy:∀ᶠ i in ψ,ClearOf 0 (y i) c): ∃ f:V→ℝ,Score ψ T f∧ ∀ᶠ i in ψ,∀ x:X→ E4,Ridge (s i) η M D Q x → ‖observe (spectator U (r i)) (beside (picked _ x) (y i)) (beside p q) - P.truncated (spectator U (r i)) d (picked _ x) p 0 (y i) q‖ * V' i/(s i ⊥)^(d+1)≤f i:=by
    obtain ⟨l,hl⟩:= total_cast (M:=M+1) D r y q H p P d hc hy (by positivity:0<η/2); obtain ⟨g,hg,he⟩:= pol_error (b:=1) U hP A D p (H.fresh (η/2) (by positivity)) hL h le_rfl (by positivity :0≤M+1) q 2 d hc
    obtain ⟨f,hf,hκ⟩:= Auth.encode (A:=l) D A h.simpleGate H (weighing D p H (d+1)) hl (by norm_num) hη hg (B:=1) (by filter_upwards [he,hy] with i h hk x hx hv; refine le_trans (le_of_eq ?_) (h x (enhanced D H 2 x _ _ hx hv) (y i) hk (r i)); ring)
    refine ⟨f,hf,hκ.mono fun i h x hx=>?_⟩; refine le_trans (le_of_eq ?_) (h _ hx); ring
end YM.OPE.Arboreal.Trace
