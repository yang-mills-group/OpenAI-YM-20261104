import YM.Integration.WilsonConditionalTaylorMarkedRows
import YM.Integration.WilsonConditionalTaylorMarkedWaves

/-! One normalized Wilson step with a genuinely variable vacuum and an
arbitrary genuinely variable signed joint insertion, on a positive rooted
strip. All invoices concern the incoming unblocked fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedPass
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open WilsonConditionalTaylorBulkRows WilsonConditionalTaylorBulkShape WilsonConditionalTaylorMarkedInlet WilsonConditionalTaylorMarkedRows
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t l : ℕ} (P : Flight j t) (L : Lodge P.patch) (W Z : Pot G)
    (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : ∀ n, (primary P.patch K n).Choices)
    (U V : (n : Side)→Pap (wire G n))

theorem full (hp : Vivid W) (hr : LocalRatio ρ) (room : 4≤t) (E d u : ℕ) (hu : l≤u)
    (head : ∀ n, coeff 0 (U n)=crunch (kernelP G K.penalty P.wing n)) (old : ∀ n,Ranks (U n))
    (sky : Young Z l) (marked : ∀ n,Young (rancho (V n)) l) (x : edgeL G) (y : Loc G 1)
    (vacuum : ∀ a ≤ E, ∀ r,0<r → r≤E+2 → ∃ w:ℝ,0<w ∧ Kith w (W a r) (fun n=>rancho (U n) a r))
    (source : ∀ a ≤ E, ∀ r ≤ l+E,∃ w:ℝ,0<w ∧ Kalm w x (Z a r) (fun n=>rancho (V n) a r)) :
    ∃ s:ℝ,0<s ∧ Kalm s (chief P x y) (braise P L W Z ρ h u E d)
      (fun n=>rancho (Reef.tossed P ρ h L n (k n) (U (n*P.L)) (V (n*P.L))) E d) :=by
  obtain ⟨w,wp,C,C0,gamma,whole⟩:=WilsonConditionalTaylorMarkedWaves.all P L W ρ h k U hp hr room E old vacuum
  let o : Biglot (BoardL G P.patch L):=coastRight _ _ _ (chief P x y)
  let T:=coves K P L Z
  let B(n : Side):=rancho (bank P L h n (V (n*P.L)))
  have incoming(a : ℕ)(ha:a≤E)(r : ℕ)(hr':r≤l+E) : ∃ b:ℝ,0<b ∧ Kalm b o (T a r) (fun n=>B n a r) :=by
    obtain ⟨v,positive,spent⟩:=source a ha r hr'
    exact sourced P L h room Z V x y a r positive spent
  have valid(n:Side):Young (B n) l:=income P L h n _ room (marked _)
  obtain ⟨b,bp,held⟩:=WilsonConditionalTaylorMarkedWidths.marked (Kemp.convict (K:=K) P L Z sky) valid incoming
  let s:=min w b
  have pos:0<s:=lt_min wp bp
  have heat:=strip_mono gamma (min_le_left w b) (le_refl C)
  let q:=rayshot P L h
  have grant(i:ℕ):Kalm s o (border P L W Z ρ h i E d)
      (fun n=>dates P L ρ h n (k n) (U (n*P.L)) (V (n*P.L)) i E d) :=by
    exact kalm_group i E E d (lands q) q.acts (fun a e r _ he hr'=> kith_ebb (whole a e he r hr') (min_le_left ..))
      (fun e r he=>WilsonConditionalTaylorMarkedWidths.narrower (min_le_right ..) (held e he r)) le_rfl
      (landing_row q (Row.rights _ _ (rayStrip P L h C0 heat) pos.le)) pos (.of_forall (ray_grated P L h pos.le C0 heat)) (ray_flip P L h)
  refine ⟨s,pos,?_⟩
  have each(n : Side):=WilsonConditionalTaylorMarkedRows.read P L ρ h n (k n) (U (n*P.L)) (V (n*P.L)) hr room (head _) (old _) (marked _) u hu E d
  simp only [each,braise]
  exact kalm_many _ (fun i _=>kalm_cut (grant i))

end YM.Integration.WilsonConditionalTaylorMarkedPass
end

