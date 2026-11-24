import YM.Qlocal.Quipu.Rhythm
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
namespace Macarons
open Tender
variable {m j k0 ℓ r':ℕ}
variable (s:Senses R)(z:α→ Site n)(O:Lattice.Order)(Y:Zora.Noon G N)
    (T: Tune ((Coarse G)⊕α)) (h:T.typeR.Good a b k)(ha:0<a)(t:ℕ)(x: Ker.rule (Coarse G) n)
    (hq:k≤N)
set_option quotPrecheck false
local notation "K"=> k-(essence s).card -- parentheses important
local notation "T0"=> Fin (k-(essence s).card+1)
set_option quotPrecheck false
local notation "P"=> how T s Y O hq h
local notation "μ"=> payQ s z O Y T x j
local notation "μ₀"=> payQPiece s z O Y T x j
local notation "f₀"=> ree s z O Y T h t hq
local notation "Ξ"=> litTPiece s z O Y T h t x hq j
local notation "Π₀"=> litT s z O Y T h t x hq j
-- short exact care.L
variable (i : ℕ) (hw:Dais.good s.val (Dais.chain (T.slip i)))
set_option quotPrecheck false
local notation "w"=> T.slip i
local notation "s₀"=> (essence s).card
local notation "r₀"=> (List.length (Dais.coin (T.slip i)))
-- budgets.World.v seats Test before any ℤ.Point.Pays all periods & wounds
noncomputable abbrev brick (k r t:ℕ)(d u:ℝ) (Y:Zora.Noon G N):=Vase.capita G r t t (ivory G t d) u*Ballad.postage Y k r u
variable (U:ℝ) (hU:0<U)(ht:U*(5*k:ℝ)≤a/2) {d ℓ':ℝ}(hw':‖x‖≤1) (hL:PaintSupply G (t+1) d)(hh:Allows (t+1) G.plog 1 ℓ')
    (he:j+(k-(essence s).card) ≤ t)
noncomputable abbrev freight (Y:Noon G N)(k k' t:ℕ)(d u:ℝ):= ∑ i: Fin (k'+1),brick k i t d u Y
noncomputable abbrev crest (T:Tune ((Coarse G)⊕α))(a:ℝ):= T.typeR.price (a/2)
include hL
lemma paints : PaintSupply G t d:= ⟨hL.1,fun i hi=> (hL.2 i hi).order t.le_succ⟩
include hL hU
lemma brick_ge(r:ℕ):0≤brick k r t d U Y:= mul_nonneg (Vase.capita_ge _ _ _ _ (ivory_ge (paints t hL)) hU) (mul_nonneg (bill_pos ..) (Real.exp_pos _).le)
lemma freight_ok(q:ℕ) : 0 ≤ freight Y k q t d U:= Finset.sum_nonneg fun i _=> brick_ge Y t U hU hL _
include h hU ht ha he hw'
lemma lpaid : ‖Ξ i‖ ≤ freight Y k (k-(essence s).card) t d U * crest T a i:=by
 let p:=(z (Sonnet.root s)); let F:= P; let f(v:ℕ):= crest T a v; have hw:= happy_paid x hw' (paints t hL); unfold litTPiece freight; rw [Finset.sum_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun r hv=>?_; let W:= P r i; let l:= brick k r t d U Y; let f':= f₀ r i; have hr:r.val ≤ k-(essence s).card:=Nat.le_of_lt_succ r.isLt; have hm:W.fare U ≤ Ballad.postage Y k r U * crest T a i:= Ballad.paid_step T s Y O i hq (h.debt (half_le_self ha.le) le_rfl le_rfl) hU ht
 let g:=f' ∘ passing x; have hx:ContDiffAt ℝ ω g 0:= witnessed ..; have hy:Brush t (l*f i) 1 g 0 := by
    unfold g f' ree; split; swap; · exact (Brush.certified zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact mul_nonneg (brick_ge Y t U hU hL _) ((T.typeR).price_nonneg ..) ) le_rfl
    let hv:= Vase.palace W p hw t hU; refine hv.climb ?_ le_rfl; exact (mul_le_mul_of_nonneg_left hm (Vase.capita_ge G _ _ _ (ivory_ge (paints t hL)) hU)).trans_eq ((mul_assoc ..).symm)
 exact Tracks.per_jet (show Allows t g 0 (l*f i) from ⟨hx,(Brush.offer.mp hy).inside⟩) (by omega)
local notation "b₀"=> (k-(essence s).card)
local notation "Λ'"=> (leaning G n (t+1) d ℓ')
noncomputable abbrev rentS(Y:Zora.Noon G N):=∑ i∈Y.samples.support,|Y.samples i|
local notation "d0"=>Tracks.pawnout t b₀ (leaning G n (t+1) d ℓ')
include hh
omit ht hU
lemma paceQ : ‖μ₀ i‖ ≤ rentS Y*Tracks.pawnout t (k-(essence s).card) (leaning G n (t+1) d ℓ') * crest T a i:=by
 let u(χ:G.El):=lifts O (z (Sonnet.root s)) χ x; let f(χ:G.El):=unmapped s z T (u χ) i; have hX:0≤ d0 := Tracks.pawned (leaning_ge hL hh n); have he':j≤t:= (Nat.le_add_right ..).trans he; have ht(χ:G.El): ‖someJ (f χ) j‖≤Tracks.pawnout t (k-(essence s).card) (leaning G n (t+1) d ℓ'):= by
    unfold f unmapped; split; swap; · simpa only [get_height,norm_zero]
    rename_i h0; split; swap; · simpa only [get_height,norm_zero]
    simpa only [one_mul] using Tracks.verity (a:=1) (Ink.Prices.up (Dais.enough h0 (h.length i)) (Ink.Field.ticket (Dais.there z h0) _)) (lent O (z (Sonnet.root s)) χ x hw' hL hh) he'
 unfold payQPiece; rw [norm_mul,mul_comm ‖T.fee i‖]; apply mul_le_mul; rotate_left
 · apply le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp ?_); positivity
 · exact norm_nonneg _
 · exact mul_nonneg (by unfold rentS; positivity) hX
 apply (norm_sum_le ..).trans; unfold rentS; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)
-- exponentially smaller transferred width.Price by t.Context.Ω.Year.Last
omit he hL hh hw'
lemma long_time (he: n.val ≤ 2*(meter (T.slip i)+1)) : crest T a i ≤ Real.exp (a/2)* dearth (a/4) n * T.typeR.price a i:= by
 let v:ℝ:= meter (T.slip i); let b:=a/4; let L:= (n.val:ℝ); let m0:= -(a/4*(n.val:ℝ)); unfold crest dearth Ink.Field.price; rw [← mul_assoc _ _ |T.typeR.fee i|]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [←Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; have h' : L ≤ 2*(v+1):= (by unfold v L; exact_mod_cast he); change (a/2)* v ≤ ((a/2)+ - (a/4)*L)+a*v; nlinarith
noncomputable abbrev mount (k k' t:ℕ)(Y:Noon G N)(n:Side)(d ℓ' u a:ℝ):=(freight Y k k' t d u+rentS Y*Tracks.pawnout t k' (leaning G n (t+1) d ℓ'))* Real.exp (a/2)
local notation "R0"=> mount k b₀ t Y n d ℓ' U a
include hU hL hh
omit h ha
lemma positive_m : 0≤ mount k (k-(essence s).card) t Y n d ℓ' U a:= by apply mul_nonneg (add_nonneg (freight_ok Y t U hU hL _) (mul_nonneg _ (Tracks.pawned (leaning_ge hL hh n)))) (Real.exp_pos _).le; unfold rentS; positivity
include h ha hw' hU ht he
lemma cumul : ‖ Ξ i-μ₀ i‖ ≤ R0 * dearth (a/4) n*T.typeR.price a i:= by
 by_cases hx: n.val ≤ 2*(meter (T.slip i)+1); swap; · rw [sawn s z O Y T h t x hq i (Nat.lt_of_not_ge hx) he, sub_self,norm_zero]; exact mul_nonneg (mul_nonneg (positive_m s Y t U hU hL hh) (Real.exp_pos _).le) (h.pay.1 i)
 let v:=crest T a i; let F:=freight Y k (k-(essence s).card) t d U; let H:= rentS Y*d0; have ht0:0≤F:=freight_ok Y t U hU hL _; have he0:0≤H:= by unfold H; exact mul_nonneg (by unfold rentS; positivity) (Tracks.pawned (leaning_ge hL hh n)); -- Lean syntax semicolon
 apply (norm_sub_le ..).trans ((add_le_add (lpaid s z O Y T h ha t x hq i U hU ht hw' hL he) (paceQ s z O Y T h ha t x i hw' hL hh he)).trans ?_)
 rw [←add_mul]; apply le_trans (mul_le_mul_of_nonneg_left (long_time T h ha i hx) (add_nonneg ht0 he0)); -- name args
 unfold mount; apply le_of_eq; ring
lemma boutique : ‖litT s z O Y T h t x hq j-payQ s z O Y T x j‖≤ mount k (k-(essence s).card) t Y n d ℓ' U a * b*dearth (a/4) n:= by
 let l:= R0*dearth (a/4) n; have he' (i:ℕ): ‖(Ξ i-μ₀ i)‖ ≤ l*T.typeR.price a i:= cumul s z O Y T h ha t x hq i U hU ht hw' hL hh he; let hel:HasSum (fun i=> Ξ i - μ₀ i) ((Π₀) - μ) := (codeT s z O Y T h ha t x hq U hU (ht.trans (half_le_self ha.le)) (j:=j)).sub (codeQ s z O Y T h ha x (j:=j)); let f:=fun i:ℕ=> ‖Ξ i-μ₀ i‖; let u:= T.typeR.price a; have hhs:Summable (fun i:ℕ=>l*u i) := (h.pay.2.1.mul_left l); have hx:Summable f := hhs.of_nonneg_of_le (fun i=> norm_nonneg _) he'; rw [← hel.tsum_eq]; refine (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he' hhs).trans ?_); rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left (h.pay.2.2) (mul_nonneg (positive_m s Y t U hU hL hh) (Real.exp_pos _).le)).trans_eq (mul_right_comm ..)
end Macarons
end Incline
end YM.Qlocal.Quipu.Eluder
