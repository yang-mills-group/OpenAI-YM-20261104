import YM.OPE.Compatible.Spa.Ara
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
include H
omit H
variable {B:ℕ→ Q→Submodule ℝ F}{Y':Q→ Submodule ℝ F}{W:(e:Fin d)→(m:Q)→ B e.val m→ₗ[ℝ] Jewel (V e)}{g':F→ₗ[ℝ] F}{S:(e:Fin d)→(m:Q)→ Jewel (V e)→ₗ[ℝ] B e.val m}
variable (P:Pipes B Y' W g' S)(m:M)(n:Q)
noncomputable def Race (x:E→ₗ[ℝ] F): Mel V→ₗ[ℝ] Mel V:= (P.port n).comp (x.comp (bulk R m)) -- need H for role
include H P
lemma over (p:M)(q:Q)(x:E→ₗ[ℝ] F)(u:E)(h:∀ y:E,y∈Bay A Y d p→x y∈Bay B Y' d q): P.port q (x u)= Race (R:=R) P p q x (H.port p u):=by
       have hv:= (P.worthM q|>.hero _).1 (h _ (H.worthM p|>.slice u)); rw [map_sub,map_sub] at hv; exact sub_eq_zero.mp hv
lemma RaceTrim (x:E→ₗ[ℝ] F)(p:Mel V)(i:ℕ)(ht:i ≤ d)(hx:∀ y:E,y∈Bay A Y i m→x y∈Bay B Y' i n)(h:trims i p) :trims i (Race (R:=R) P m n x p):=by
       apply (P.port_zero n i ht _).1; exact hx _ (le_sup_left (a:=A i m) (H.burst m p i h))
lemma RaceDr (x:E→ₗ[ℝ] F)(h:∀ y:E,x (g y)=g' (x y))(v:Mel V):FlowP V (Race (R:=R) P m n x v)=Race (R:=R) P m n x (FlowP V v) :=by
       change FlowP V (P.port n (x (bulk R m v)))=P.port n (x (bulk R m (FlowP V v))); rw [←P.portτ, ←h, H.sway]
noncomputable abbrev PDiag (p:Mel V→ₗ[ℝ] Mel V)(e:Fin d): Jewel (V e)→ₗ[ℝ] Jewel (V e):=(LinearMap.proj e).comp (p.comp (LinearMap.single ℝ (fun i=>Jewel (V i)) e))
omit H in lemma PDiagD (x:E→ₗ[ℝ] F)(j:Fin d)(u:Jewel (V j))(v:B j.val n)(hq:x (R j m u|>.val)-v.val∈ Y' n): PDiag (Race (R:=R) P m n x) j u=W j n v:=by
       change P.port n (x (bulk R m (Pi.single j u))) j=_; rw [bulk_single]; have ht: (P.port n) (x (R j m u|>.val))=(P.port n) v.val:=by apply sub_eq_zero.mp; rw [←map_sub]; exact (P.worthM n|>.hero _).1 (le_sup_right (a:=B d n) hq)
       rw [ht]; exact P.port_grade ..
end Pipes
end YM.OPE.Hark
