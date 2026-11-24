import YM.SignedWilsonExpansion.F9.Race
/-!
# Coast. telescope finite prices without change of voxel coordinates

Lines can incur startup costs from history N (to repaint) or matched epoch N'.
Aux evaluator uses the second clock and requires all join bills on that one.
`carry` even when alignment ends at f (index above v), still supplies one
whole-product estimate down to ℓ. No nested identification of proper marginal
history outputs is required. Products retain phases.Book.PROFILES computed at
nodes. Rental wire only uses coefficients through `max crop`.
-/
set_option autoImplicit false
set_option maxHeartbeats 740000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e s k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a:ℝ}{E W U:Credit}
variable {R: Realm G (e+1) E}{x:ℕ→Fin (n+1)→Cover}{P:ℕ→ Fin (n+1)→Era G ℝ}{θ:ℕ→ℝ}
/-- STEP-oriented payment. `fees(i,j)` same-step quote on P i and P(i+1) for
  each slot. `bound` allows positions moving by actual lengths, discharges polynomial
  distance gains inside each step before scheduling joins! -/
structure Jetty (h:Fin (n+1)→ℕ)(A:Levels G)(Ñ:ChartRatio G)(m c N:ℕ)(x:ℕ→Fin (n+1)→Cover)(u e:ℕ)(P:ℕ→Fin (n+1)→ Era G ℝ)(Q:ℝ): Prop where
   auth (i:ℕ):m≤ i→i≤ c→∀ j,Auth (h j) (P i j)
   sail (i:ℕ): m≤ i→ i<c →(x (i+1)=fun j=>childFrom A i (x i j))∧∀ j,P i j=verseI A Ñ i N (h j) (P (i+1) j)
   price (i:ℕ): m≤ i → i<c→∃ t>0, ∃ X: Fin (n+1)→ℝ,(∀ j, Respect (h j) e u 1 (P (i+1) j) (X j) ∧ Respect (h j) e u 1 (P i j) (X j)) ∧
       (∀ j k,j≠ k → t≤ (Bank.terrain.gap (x i j) (x i k):ℝ)) ∧ (t^u)⁻¹*(∏ i,X i)≤ Q
variable {K:Fin (n+1)→ℕ}
local notation "ρ" => R.draws
abbrev knotP (P:ℕ→ Fin (n+1)→Era G ℝ)(x:ℕ→Fin (n+1)→Cover)(R:Realm G (e+1) E)(N:ℕ)(i m k:ℕ):= cruises R.draws R.paid N k i m (embark (P i) (x i))
namespace Jetty
variable (f:Jetty K R.draws R.paid v c N x u e P Q)
local notation "Kτ" => (∑ i,K i)
include f
lemma plusStep (d:SpringD R k 0 u W)(g:Canopy R m c Z)(h:m≤v)(c':c≤N)(y: Kτ ≤ k)(p:v ≤ i)(t:i<c): Respect Kτ e 0 0
     (verseI ρ R.paid i N Kτ (embark (P (i+1)) (x (i+1))) - embark (P i) (x i)) ((sponsorX G n k e u E W).buy Z*Q):=by
    obtain ⟨z,hz,V,w,l,a⟩:= f.price i p t; obtain ⟨b,w'⟩:= f.sail i p t; let L(j):= verseI ρ R.paid i N (K j) (P (i+1) j); have hw:P i=L:= funext w'; let W:= sponsorX G n k e u E W
    rw [b,hw]; apply (gapCharge (P (i+1)) d K (x i) hz l y (g.arch.trans (h.trans p)) (t.trans_le c') V (fun j=>(w j).1) (fun j=>by rw [← w' j]; exact (w j).2)).rise; exact mul_le_mul (g.older W (h.trans p) t.le) a (mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _=>(w j).1.nn))) (zero_le_one.trans (W.purchase g.positive))
omit f in
def yieldT (G:Gauge)(n k k' e u:ℕ)(E W U:Credit):= (cabin G k e 0 E U).prodC (sponsorX G n k' e u E W)
lemma dated (D:Dormitory R Kτ 0 U)(d:SpringD R k 0 u W)(g:Canopy R m c Z)(h:m≤v)(c':c≤N)(y: Kτ ≤ k)(p:v ≤ i)(t:i<c): Respect Kτ e 0 0
     (knotP P x R N (i+1) m Kτ -knotP P x R N i m Kτ) ((yieldT G n Kτ k e u E W U).buy Z*Q):=by
    let T:=f.plusStep d g h c' y p t; let a:=h.trans p; let Z':=g.cut (le_refl m) a t.le; have hQ j (y':v≤ j)(v':j≤c):Auth Kτ (embark (P j) (x j)) := manCo _ K fun i=>(f.auth j y' v' i).shifted _ -- fill
    have W:= voyage D Z' (fun _=>0) Z'.bare (t.le.trans c') T; unfold yieldT; rw [Credit.products,mul_assoc]; convert W using 1; rw [cruisePlus ρ a R.hG R.green (t.le.trans c') (Auth.verse ρ (t.trans_le c') R.hG R.green (hQ _ (by omega) t)) (hQ _ p t.le),cruiseStep ρ R.paid _ a]
lemma carry (D:Dormitory R Kτ 0 U)(d:SpringD R k 0 u W)(g:Canopy R m c Z)(h:m≤v)(c':c≤N)(y: Kτ ≤ k)(u':0≤Q)(p:v≤c):
    Respect Kτ e 0 0 (knotP P x R N c m Kτ-knotP P x R N v m Kτ) ((((yieldT G n Kτ k e u E W U).prodC Credit.leanC).buy Z)*Q):=by
    let F:=fun i=> knotP P x R N i m Kτ; let C:=yieldT G n Kτ k e u E W U
    have h0:∀ i:ℕ, v≤ i → i ≤ c → Respect Kτ e 0 0 (F i-F v) (((i-v:ℕ):ℝ)*(C.buy Z*Q)):=by
       intro j b; induction j, b using Nat.le_induction with
       | base=> intro _; rw [Nat.sub_self,Nat.cast_zero,zero_mul,sub_self]; exact Respect.zero
       | succ j t ih=> intro a; rw [show F (j+1)-F v=(F j-F v)+(F (j+1)-F j) from by abel]; exact ((ih (by omega)).add (f.dated D d g h c' y t a) (le_refl 0)).rise (le_of_eq (by rw [show j+1-v=(j-v)+1 by omega, Nat.cast_add,add_mul,Nat.cast_one,one_mul]))
    apply (h0 c p le_rfl).rise; rw [Credit.products,Credit.lean_cost,mul_comm _ Z,mul_assoc]; exact mul_le_mul_of_nonneg_right ((g.cut h p le_rfl).pad.lengthS) (mul_nonneg (zero_le_one.trans (C.purchase g.positive)) u')
-- cut charts
lemma subset (p:v≤ i)(q:j≤c): Jetty K R.draws R.paid i j N x u e P Q:=⟨fun k b w=>f.auth k (p.trans b) (w.trans q), fun k b w=> f.sail k (p.trans b) (w.trans_le q), fun k b w=> f.price k (p.trans b) (w.trans_le q)⟩
end Jetty
-- assemble aligned phase via mark grid.Stock.Geometry built elsewhere from XSpace.Box
structure Cowrie (A:Levels G)(m c:ℕ)(x:ℕ→ J→Cover)(θ:ℕ→ℝ): Prop where
   bound i:m≤ i → i ≤ c → 0< θ i
   adult i :m≤ i→i<c → x (i+1)=fun j=>childFrom A i (x i j)
   room i : m ≤ i→ i<c →∀ j k,j≠k → θ i≤ (Bank.terrain.gap (x i j) (x i k):ℝ)
lemma Cowrie.cuts {x:ℕ→J→Cover}(z:Cowrie A m c x θ)(p:m≤v)(q:b≤c): Cowrie A v b x θ:=⟨fun i z' b' => z.bound i (p.trans z') (b'.trans q),fun i z' b'=> z.adult i (p.trans z') (b'.trans_le q),fun i z' b'=> z.room i (p.trans z') (b'.trans_le q)⟩
lemma Cowrie.entry (z:Cowrie A m c x θ)(ψ:ℕ→Fin (n+1)→ℝ)(h:∀ i,m≤ i →i≤ c→∀ j,Respect (K j) e u 1 (P i j) (ψ i j))(g:∀ i,m≤ i→i<c → ∀ j,ψ i j≤ψ (i+1) j)(f:∀ i,m≤ i→ i<c→∀ j, P i j=verseI A Ñ i N (K j) (P (i+1) j))(q:∀ i,m≤ i→i<c → (θ i^u)⁻¹*(∏ j, ψ (i+1) j)≤ Q): Jetty K A Ñ m c N x u e P Q:= by refine ⟨fun i p q j=> (h i p q j).auth,fun i p q=>⟨z.adult i p q,f i p q⟩,fun i p w=> ⟨_,z.bound i p w.le,ψ (i+1), fun j=>⟨h (i+1) (p.trans (by omega)) w j,(h i p w.le j).rise (g i p w j)⟩,z.room i p w,q i p w⟩⟩
end YM.WilsonCoeffUV.Mer.Xa
