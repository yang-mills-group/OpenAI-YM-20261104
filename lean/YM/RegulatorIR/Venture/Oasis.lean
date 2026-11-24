import YM.RegulatorIR.Venture.Lattice

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Crown vacuum transportation on cover. Includes exact horizontality of
rank-two adjustment tested through UNSHIFTED carrier from ANY schedule.
-/
open Epoch.League
variable {X: Type} {M:X→ℕ}{n:Page M→Side} {K:KernelChoices} (S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→Scale){r i e k u:ℕ}
local notation "T₁"=> S.devices Y G Z s
local notation "A₀"=> curtain S Y G
local notation "A₁"=> pathL S Y G
local notation "M₁"=> lnk S G
local notation "M₂"=> drifted S G

def valley (f:Flap M)(T:Packet (Foot G) r):= (T₁ f).pullI (offer (firstChannel (S.opened G f.prev) (S.opened G f.next)).native T)
def river (f:Flap M)(T:Packet (Foot G) r):= unfoldQ (fun _=> A₀ f) T
def crest (f:Flap M)(T:Packet (Foot G) r):Prop:= valley S Y G Z s f T=river S Y G f T
-- quantities.Actor expenses.Se.C.
local notation "K₀"=> valley S Y G Z s
local notation "R₀"=> river S Y G
local notation "C₀"=> crest S Y G Z s
include Y G Z s
lemma scope (p:Page M) (q:Flap M) (hk:p=q.prev): S.l p≤ S.l q.next:= hk ▸ ((S.dialect Y G Z s).climb q) -- needs Z, s
lemma price_v (p:Flap M) (k:ℕ): Billed ((T₁ p).driftL)∧ Billed (Function.swap (A₀ p))∧Billed (Function.swap (A₁ p))∧Skein.Acres (Gain.halo (A₀ p) (A₁ p)) k:=by
 let u:=0; have h:= merited S Y G u p; have ht:=spooled S Y G u p
 exact ⟨(flits S Y G Z s p).1,billed_supp h.beam.2 ht.1,billed_supp h.flows.2 ht.2,Skein.escorts _ (Tariff.native _ (S.l_p p.next) u) (localL (S.l p.prev)) (localL (S.l p.next)) (fun j _=>⟨_,show starM S Y G j u p≠⊤ from staffed _ _ _ ht.1 ht.2,living_v S Y G _ _ (scope S Y G Z s _ _ rfl)⟩)⟩
lemma receives (i:Flap M)(T:Packet (Foot G) r)(H: Limits T)(x:Tuple (Foot G) r): Summable (fun v: Tuple (Foot G) r=> T v* ∏ b:Fin r,(fun j:Fin r=> A₀ i (v j) (x j)) b):=by -- local notation arg.Notice f. Pupil.wind path.P Lens.
 let V:= leggy (A₀ i); let g:= fun z:Foot G=> Sum.inl (β:=Foot G) z; let j:= firstChannel (S.opened G i.prev) (S.opened G i.next);let p:= lastChannel (S.opened G i.prev) (S.opened G i.next)
 let f:= offer j.native T;let x':=acrossT p.native x; let t:=List.finRange r
 have he:= pricedField (offerL H j.native) V (upwardL (price_v S Y G Z s i 0|>.2.1)) x' t -- add Z.s used. issue
 let X(v):=acrossT j.native (v:Tuple (Foot G) r); apply (he.comp_injective (injectT j.native)).congr
 intro v;rw [Function.comp_apply, Gradient.field,offer_eq,if_pos];
 · unfold t; rw [List.toFinset_finRange]; rfl
 intro z hz; exact (hz (List.mem_finRange ..)).elim
variable {T P:Packet (Foot G) r}
lemma adopts (f:Flap M)(ht:Limits T)(hh:Limits P): river S Y G f (T-P)=R₀ f T - R₀ f P:=by
 ext1 i; rw [Pi.sub_apply]; unfold river unfoldQ; simp only [Pi.sub_apply,sub_mul]; exact (receives S Y G Z s _ T ht i).tsum_sub (receives S Y G Z s f P hh i)
lemma inherits (f:Flap M)(ht: Limits T)(hh:Limits P): valley S Y G Z s f (T-P)= K₀ f T - K₀ f P:=by
 let p:= firstChannel (S.opened G f.prev) (S.opened G f.next); let K':= T₁ f; have H : K'.pullI (offer p.native (T-P) + offer p.native P)= K₀ f (T-P)+K₀ f P:= pull_a _ (price_v S Y G Z s f 0|>.1) (offerL (subtracts ht hh) _) (offerL hh _)
 rw [← Diagram.offer_sum',sub_add_cancel] at H; rw [eq_sub_iff_add_eq]; exact H.symm
lemma ask_v (f:Flap M)(H: crest S Y G Z s f T) (a:ℝ): crest S Y G Z s f (a • T):=by -- unnecessary h
 unfold crest valley;rw [Sources.scaleO,pull_m]; change a • (K₀ f T)= _; rw [H];ext1 i;unfold river unfoldQ; rw [Pi.smul_apply]; change a*_ = _;simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc];exact (tsum_mul_left).symm
lemma V_house {T: Orders (Foot G)}(H:W1 T e)(hp: i ≤ e)(hh:∀ i≤ e,∀ j,Limits (T i j))(hS:gradedSymmetric T)(hQ:Ranks 2 T)(f:Flap M)(r:ℕ): (K₀ f (T i r))= R₀ f (T i r)-Gradient.correction (Gain.halo (A₀ f) (A₁ f)) T i r:=by
 obtain ⟨h,hv,hP,he⟩:=price_v S Y G Z s f e
 exact crossing (T₁ f) (A₀ f) (A₁ f) T H hQ (hS i r) hh hv hP h he rfl hp
-- carrier adjustment linear through rank2 fact β value.Ready
lemma worthy {X':Type}{M':X'→ℕ}{n':Page M'→Side}(S':Circuit M' n')(s':Page M'→Scale)(i:Flap M)(p:Page M') (u:ℝ): crest S Y G Z s i (u • coil (S'.scroll_j Y G p)):=by
 let U:= fullV S' Y G Z s' p;  let h:=V_house S Y G Z s (badge S' Y G Z s' p 0) (le_refl 0) (fun j _ r=> V_l S' Y G Z s' p j r) (V_s _ _ _ _ _ _) (grammar _ _ _ _ _ _) i 2 -- name Z shadow. need simp.Corr
 unfold Gradient.correction at h; simp_rw [V_i] at h -- changes also V_s? equations only lhs; simp removes in RHS? check
 simp at h; exact ask_v S Y G Z s i h u
lemma wick_minus (f:Flap M)(h:C₀ f T)(hp:C₀ f P)(ht:Limits T)(hh:Limits P): C₀ f (T-P):=by unfold crest; rw [adopts S Y G Z s f ht hh,inherits S Y G Z s f ht hh,h,hp]
end YM.RegulatorIR.Venture
