import YM.Integration.WilsonConditionalTaylorBulkRows

/-! Positive strip thermodynamic continuity of the full nonlinear Wilson
vacuum for a changed finite predecessor with all its true incoming wires.
Widths are bought jointly for finitely many grades/ranks before traversing
the connected Wick graphs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkContinuity
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open WilsonConditionalTaylorBulkRows
open scoped Topology BigOperators Classical

private theorem widths {I : Type} [Fintype I] [DecidableEq I] (E : ℕ) {A : OrbitV (Biglot I)}
    {Z : (n : Side)→OrbitV (Tor n I)} (sky : Fiery A) (torus : ∀ n, Fiery (Z n))
    (paid : ∀ e ≤ E, ∀ r, 0 < r → r ≤ E+2 → ∃ s : ℝ, 0 < s ∧ Kith s (A e r) (fun n=>Z n e r)) :
    ∃ s : ℝ, 0 < s ∧ ∀ e ≤ E, ∀ r, 0 < r → Kith s (A e r) (fun n=>Z n e r) := by
  let Finite:=Fin (E+1)×Fin (E+2)
  have fee(i:Finite):∃ s : ℝ, 0 < s ∧ Kith s (A i.1 (i.2.val+1)) (fun n=>Z n i.1 (i.2.val+1)):=
    paid _ (by have:=i.1.isLt;omega) _ (by omega) (by have:=i.2.isLt;omega)
  choose w w0 billed using fee
  obtain ⟨v,_,min⟩:=Finset.exists_min_image Finset.univ w ⟨(0,0),Finset.mem_univ _⟩
  refine ⟨w v,w0 v,?_⟩
  intro e he r hr
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  by_cases low:j < E+2
  · let i : Finite := (⟨e,by omega⟩,⟨j,low⟩)
    exact kith_ebb (billed i) (min i (Finset.mem_univ _))
  have sky0:A e (j+1)=0:=by by_contra nz;have a:=(sky e _ nz).2.1;omega
  have torus0(n):Z n e (j+1)=0:=by by_contra nz;have a:=(torus n e _ nz).2.1;omega
  simp only [sky0,torus0]
  exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun n=>bail_void ..⟩

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (W : Pot G)
    (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : ∀ n, (primary P.patch K n).Choices)
    (U : (n : Side)→Pap (wire G (n*P.L)))

/-- The independent cover output is approached by the *changed* genuine
finite normalized vacuum. Its only convergence invoices are on the finite
predecessor before the connected Gaussian contractions. -/
theorem contraction (hp : Vivid W) (hr : LocalRatio ρ) (room : 4 ≤ t) (e r : ℕ) (rank : 0 < r)
    (head : ∀ n, coeff 0 (U n)=crunch (kernelP G K.penalty P.wing _))
    (shape : ∀ n, Fiery (rancho (inlet P L ρ h n (k n) (U n))))
    (prior : ∀ a ≤ e+1, ∀ d, 0 < d → d ≤ e+1+2 → ∃ s : ℝ, 0 < s ∧
      Kith s (cola W ρ P L K a d) (fun n=>rancho (inlet P L ρ h n (k n) (U n)) a d)) :
    ∃ s : ℝ, 0 < s ∧ Kith s (waken P L W ρ h (e+1) r)
      (fun n=>rancho (Reef.landed P ρ h L n (k n) (U n)) (e+1) r) := by
  let X:=cola W ρ P L K
  let Z(n : Side):=rancho (inlet P L ρ h n (k n) (U n))
  obtain ⟨w,wp,purchased⟩:=widths (e+1) (Bank.fairy W ρ P L K hp hr) shape prior
  obtain ⟨z,B,zp,strip⟩:=(gamma_ready G K P L h).1
  let s:=min z w
  have positive:0 < s:=lt_min zp wp
  have B0:0 ≤ max 0 B:=le_max_left ..
  have geom:=(strip_mono strip (min_le_left z w) (le_max_right 0 B))
  let q:=rayshot P L h
  have dots (a d : ℕ) (hd : 0 < d) : Kith s (stopper X (e+1) a d) (fun n=>stopper (Z n) (e+1) a d):=by
    unfold stopper
    by_cases ha:a ≤ e+1
    · simp only [if_pos ha];exact kith_ebb (purchased a ha d hd) (min_le_right ..)
    simp only [if_neg ha]
    exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
  have graph (i : ℕ) : Kith s (swim (lands q) X i (e+1) r) (fun n=>swim (q.acts n) (Z n) i (e+1) r):=by
    have v:= kith_swim (landing_row q (Row.rights _ _ (rayStrip P L h B0 geom) positive.le)) _ positive
      (.of_forall (ray_grated P L h positive.le B0 geom)) (ray_flip P L h) dots i (e+1) r rank
    rw [through_swim (lands q) (stopper X (e+1)) X i (e+1) (fun j hj=>if_pos hj) (e+1) le_rfl] at v
    have edge(n : Side) : swim (q.acts n) (stopper (Z n) (e+1)) i (e+1)=swim (q.acts n) (Z n) i (e+1):=
      through_swim _ _ _ _ _ (fun j hj=>if_pos hj) _ le_rfl
    simpa only [edge] using v
  have original : Kith s (coastRun P L W ρ h (e+1) r) (fun n=>connected P L ρ h n (k n) (U n) (e+1) r):=
    kith_many _ fun i hi=>boarded (graph i)
  have each(n):=WilsonConditionalTaylorBulkRows.read P L ρ h n (k n) (U n) hr room (head n) (shape n) e r
  refine ⟨s,positive,?_⟩
  simp only [waken,if_neg (Nat.succ_ne_zero e),if_neg (Nat.ne_of_gt rank),each]
  exact original

end YM.Integration.WilsonConditionalTaylorBulkContinuity
end

