import YM.RG12.Alidade.Fades
import YM.RG12.Alidade.Parasol
/-!
# Interpret actual k-cards and the one crucial gap in using these for sharp prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Filter Finset Set Wilson Lattice RG Source Real Frames Commission Rail
open Extraction Bid MergeProof Org Spec PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired YM.Pert.Dense
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{d:ℕ}
variable {U:Final C f S} {Q:OPE.Prescription U.sector.derivatives}{hQ:Q.Coherent}
variable {φ:Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}
variable {P:Port C}{lit:ℕ→Prop}{W:Worth}{u ψ σ δ:ℕ→ℝ}{r:ℕ→ℕ}
variable (h:G.Simple)(hO:Observing C U.room.cutoff φ M)
variable {i:Fin 3}{ax:Axis}
set_option quotPrecheck false
local notation "Z!"=>C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "clk"=>epoch C.path.levels
local notation "arc!"=> (P.panels d i).arc
local notation "B!"=> U.sector.derivatives
local notation "X!"=> wheelR U d
variable {Y:ℕ → Col (wheelR U d)≃ₗ[ℂ] S.Field d}{Z:ℕ→TableL C d}{N:ℕ}{K:ℝ}{p:ℕ}
variable (HC:Club M P U Q hQ φ d N ax lit i Z Y K p)
variable (hB:Beacon C.path.levels P.rate lit)(hr:Slurry C.path.levels)
include h hO hB HC hr
lemma attach {s b:ℕ}{e:ℕ→ℝ}(H:let t:=torchR (Z!) arc! N;Clearing (Z!) Y (lens U d ax N ∘ t) t e s b lit K) :
    RightTab (interest e (pursePower d s b)) C S M d ∧ ∀ w:ℕ,RowTab (interest e (pursePower d s b)) C S U.sector.derivatives M d w:=by
   obtain ⟨Q',hQ'⟩:=journey h hB hr U.room.cutoff hO HC.active HC.calendar.2 H HC.calendar.1
   exact ⟨inward HC.land hQ' h U.room.cutoff hO, outward HC.land hQ' h U.room.cutoff hO⟩
-- export for all filters or consumers. K not clocked in power: can pay once by power increase.
omit hO hB hr in
lemma filings : let t:=torchR (Z!) arc! N;let e:=(fun k=>min 1 (4*K*fineprint C.path.levels (trays d) k))
    Clearing (Z!) Y (lens U d ax N ∘ t) t e 1 0 lit K:=by
   intro t e
   have hK:0 ≤ 4*K:=by have hκ:=HC.numbers.2; linarith only [hκ]
   have he:Tendsto (fun i=>4*K*fineprint C.path.levels (trays d) i) atTop (nhds 0):=by
      have hh:= cutoff_pos (trays d) (show 1≤trays d by unfold trays;omega)
      have hv:=((bill_hi (show -cut₀ (trays d)<0 by linarith)).comp (year_late C.path.levels h)).const_mul (4*K)
      simpa [fineprint] using hv
   refine ⟨fun i=> ⟨le_min (by norm_num) (mul_nonneg hK (Real.exp_pos _).le),min_le_left ..⟩,?_⟩
   let g:=lens U d ax N ∘ t
   filter_upwards [HC.active,(tendsto_add_atTop_nat 1).eventually HC.active,HC.wears,he.eventually (ge_mem_nhds zero_lt_one)] with k h1 h2 h3 h4 hx hz
   obtain ⟨hS,H⟩:= h3 hx hz
   let v:=t k/t (k+1); have hv:1 ≤ v:=hS
   have hb:1≤epoch C.path.levels (k+1)/epoch C.path.levels k:= epoch_unit (Z!) (Nat.le_succ k)
   have hl := zero_lt_one.trans_le hv
   refine ⟨hl,le_rfl,LinearEquiv.refl ℂ _,(h1 hx).costs,(h2 hz).costs,pace_form (Y k) (Y (k+1)) (h1 hx).wage (h2 hz).wage hl,⟨?_,fun _ _=> ?_⟩,?_,?_⟩
   · intro i j h v; change Pi.single j v i = 0; exact Pi.single_eq_of_ne (ne_of_gt h) _
   · exact Pi.single_eq_same ..
   · simp
   intro x
   let r:= (clk (k+1)/clk k)*Real.exp (e k)
   have hs : 1+4*K*fineprint (Z!) (trays d) k ≤ r:=by
      have hh:e k= 4*K*fineprint (Z!) (trays d) k:=min_eq_right h4
      rw [show 1+_=4*K*fineprint (Z!) (trays d) k + 1 from add_comm .., ← hh]
      exact (Real.add_one_le_exp _).trans (le_mul_of_one_le_left (Real.exp_pos _).le hb)
   obtain ⟨hx,hz⟩:= H x
   change g k ((Y k) ((pace (Y k) (Y (k+1)) _ hl) x)) ≤ r^1*g (k+1) (Y (k+1) x) ∧ g (k+1) (Y (k+1) x) ≤ r^1*g k (Y k ((pace (Y k) (Y (k+1)) _ hl) x))
   rw [pace_at,LinearEquiv.apply_symm_apply,pow_one]
   exact ⟨hx.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)),hz.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))⟩

local notation:max "paid" D:max=> exp ∘ (fun k=>D*quote (Z!) (trays d) k)
-- explicit remainder exponent tier. absorbed constant lifetimes for C. Larger d horizons consume later.
lemma melts : (∀ x:S.Field d, ∃ A:ℝ,0 ≤ A ∧ ∀ᶠ k in atTop, ∃ v:C.label d,S.project d (M d k v)=x∧mass C d v ≤ (paid A) k) ∧
    (∀ w:ℕ,∀ x:S.Field d→ₗ[ℂ] ℂ, ∀ hw:w≤d,(∀ e:ℕ,∀ he:e<w,∀ y:S.Field e,x (U.sector.derivatives.rise (he.le.trans hw) y)=0)→
      ∃ A:ℝ,0 ≤ A∧∀ᶠ k in atTop,∀ v:C.label d, ‖x (S.project d (M d k v))‖ ≤ (paid A) k/C.S.a k^(d-w)*mass C d v):=by
    obtain ⟨h1,h2⟩:= attach h hO HC hB hr (filings h HC)
    have hK:0 ≤ 4*K:=by have hh:=HC.numbers.2; linarith only [hh]
    constructor
    · intro x
      obtain ⟨s,hx⟩:=h1 x
      obtain ⟨A,hA,he⟩:=radian (Z!) h (trays d) s (pursePower d 1 0) _ (4*K) hK (fun i=>show min 1 (4*K*fineprint C.path.levels (trays d) i) ≤ _ from le_rfl)
      exact ⟨A,hA,(hx.and he).mono (fun _ hi=> let ⟨v,hv,hv'⟩:=hi.1; ⟨v,hv,hv'.trans hi.2⟩)⟩
    intro w x hw hh
    obtain ⟨s,hx⟩:=h2 w x hw hh
    obtain ⟨A,hA,he⟩:=radian (Z!) h (trays d) s (pursePower d 1 0) _ (4*K) hK (fun i=>show min 1 (4*K*fineprint C.path.levels (trays d) i) ≤ _ from le_rfl)
    exact ⟨A,hA,(hx.and he).mono (fun k hi v=> (hi.1 v).trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hi.2 (pow_nonneg (C.S.a_pos k).le _)) (mass_nonneg ..)))⟩

lemma supplied_if {s b:ℕ}(H:Clearing C.path.levels Y (lens U d ax N ∘ torchR C.path.levels arc! N) (torchR C.path.levels arc! N) (fun _=>0) s b lit K):RightPrice C S M d∧ ∀ w:ℕ,RowPrice C S (B!) M d w:=by
    obtain ⟨h1,h2⟩:= attach h hO HC hB hr H
    have he:∀ᶠ i in atTop, interest (fun _=>0) (pursePower d s b) i ≤ χ i ^ 0:=Eventually.of_forall (fun _=> by simp [interest])
    exact ⟨right_zero h1 he,fun w=> row_zero (h2 w) he⟩
end YM.RG12.Alidade
