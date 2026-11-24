import YM.Integration.WilsonConditionalTaylorMarkedRetile

/-! One strictly positive paid width for the finite rank and order sets
which the normalized signed contractions genuinely consult. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedWidths
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open scoped Topology ENNReal BigOperators Classical

theorem finite (E R : ℕ) (P : ℕ→ℕ→ℝ→Prop) (paid : ∀ e ≤ E, ∀ r ≤ R, ∃ w : ℝ,0<w ∧ P e r w)
    (reduce : ∀ e r s w, s≤w → P e r w → P e r s) : ∃ s : ℝ,0<s ∧ ∀ e ≤ E, ∀ r ≤ R,P e r s :=by
  let V:=Fin (E+1)×Fin (R+1)
  have item(v:V):∃ w:ℝ,0<w ∧ P v.1 v.2 w:=paid _ (by have:=v.1.isLt;omega) _ (by have:=v.2.isLt;omega)
  choose w hp hg using item
  obtain ⟨v,_,low⟩:=Finset.exists_min_image Finset.univ w ⟨(0,0),Finset.mem_univ _⟩
  refine ⟨w v,hp v,?_⟩;intro e he r hr
  let a : V:=(⟨e,by omega⟩,⟨r,by omega⟩)
  exact reduce e r _ _ (low a (Finset.mem_univ _)) (hg a)

variable {I : Type} {E l : ℕ} {x : Biglot I} {A : OrbitV (Biglot I)} {B : (n:Side)→OrbitV (Tor n I)}

theorem narrower {r : ℕ} {T : Tile (Biglot I) r} {U : (n:Side)→Tile (Tor n I) r} {s w : ℝ}
    (small : s≤w) (fee : Kalm w x T U) : Kalm s x T U :=by
  obtain ⟨li,C,hi⟩:=fee
  exact ⟨li,C,hi.mono fun n hn=>penn_shrink hn small⟩

theorem marked (sky : Young A l) (torus : ∀ n,Young (B n) l)
    (prior : ∀ e ≤ E, ∀ r ≤ l+E, ∃ w : ℝ,0<w ∧ Kalm w x (A e r) (fun n=>B n e r)) :
    ∃ s : ℝ,0<s ∧ ∀ e ≤ E, ∀ r,Kalm s x (A e r) (fun n=>B n e r) :=by
  obtain ⟨s,pos,all⟩:=finite E (l+E) _ prior (fun _ _ _ _=>narrower)
  refine ⟨s,pos,?_⟩;intro e he r
  by_cases low:r≤l+E
  · exact all e he r low
  have a:A e r=0:=by by_contra live;have z:r≤l+e:=sky e r live;omega
  have b(n):B n e r=0:=by by_contra live;have z:r≤l+e:=torus n e r live;omega
  simp only [a,b]
  exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>⟨le_rfl,by simp⟩⟩

theorem vacuum (sky : Fiery A) (torus : ∀ n,Fiery (B n))
    (prior : ∀ e ≤ E, ∀ r,0<r → r≤E+2 → ∃ w : ℝ,0<w ∧ Kith w (A e r) (fun n=>B n e r)) :
    ∃ s : ℝ,0<s ∧ ∀ e ≤ E, ∀ r,0<r → Kith s (A e r) (fun n=>B n e r) :=by
  let P:=fun e r w=>Kith w (A e (r+1)) (fun n=>B n e (r+1))
  have h:∀ e ≤ E,∀ r ≤ E+1,∃ w : ℝ,0<w ∧ P e r w :=fun e he r hr=>prior e he (r+1) (by omega) (by omega)
  obtain ⟨s,pos,all⟩:=finite E (E+1) P h (fun _ _ _ _ hs hh=>kith_ebb hh hs)
  refine ⟨s,pos,?_⟩;intro e he r hr
  obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  by_cases low:r≤E+1
  · exact all e he r low
  have a:A e (r+1)=0:=by by_contra live;have z:=(sky e _ live).2.1;omega
  have b(n):B n e (r+1)=0:=by by_contra live;have z:=(torus n e _ live).2.1;omega
  simp only [a,b];exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun n=>bail_void ..⟩

end YM.Integration.WilsonConditionalTaylorMarkedWidths
end

