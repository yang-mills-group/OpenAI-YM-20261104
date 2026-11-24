import YM.RGComparison.Core16.Silk.Samite
/-!
# Bounded shape shipment of the Fk conditional germs

Used via actual gauges of neighboring/replicated volumes, not assuming period removal externally.
`Per.Momentum → Kernel` additionally needs winding price even for unmarked term, source mounts
instead of copies, conversion included separately. Witness forest data bound through θ payments
not asserting correspondence globally after pressing winding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset Matrix
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S F:Side}{ι J k K T Y A D L : Type}[Fintype ι][Fintype J][Fintype k][Fintype K][Fintype T][Fintype Y][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D}{P:Planet X S ι k T}{Q:Planet X F J K Y}{o:ι→ℕ}{f:ι→J}{s:k→K}
   (H:P.Steady)(I:Q.Steady) (V:Overset P Q f s)(R:Rail G J→Roll)

include V H

-- reorganize toll before consiting copy f. No std-jet commuting lost support; mask
-- budgets already from P.Step clocks attached.
def farm (P: Planet X S ι k T)(R : Rail G ι→Roll)(u:Rail G ι) (i:Wire G ι) (a:k) :=
   ∑ j∈ P.soil a, ∑ w : G.ColorIndex, shelfH X (P.glyph a) (P.tip a i) (P.tip a (j,w)) • R ((j,w)::u)
omit V [Fintype A] in
private lemma paid (R : Rail G ι→Roll)(u:Rail G ι)(i:Wire G ι) : stepLaw P i R u=∑ a∈P.within i.1, farm P R u i a:= by
     let v (j: Wire G ι)(a:k) := shelfH X (P.glyph a) (P.tip a i) (P.tip a j) • R (j::u)
     have hv {a:k}{j:Wire G ι}(h:a∉P.within i.1 ∨ j.1∉ P.soil a): v j a=0:= by
        unfold v; rcases h with h|h
        · rw [tip_absent H a i (fun he=>h ((P.in_heat ..).1 he)),map_zero]; simp
        rw [tip_absent H a j h,map_zero,zero_smul]
     unfold stepLaw Planet.plank; simp_rw [Matrix.of_apply,sum_smul]; change ∑ j,∑ a,v j a=_
     rw [show (∑ j : Wire G ι,∑ a,v j a)=∑ a∈ P.within i.1,∑ j,v j a from ?_]; swap; rw [Finset.sum_comm]; exact (sum_subset (subset_univ _) fun i _ he=> sum_eq_zero (fun j _=>hv (.inl he))).symm
     apply sum_congr rfl; intro a ha; rw [Fintype.sum_prod_type]; exact (sum_subset (subset_univ _) fun i _ he=> sum_eq_zero (fun j _=> hv (.inr (show _ from he)))).symm
include I
omit [Fintype A] in
lemma toll (u:Rail G ι)(i:Wire G ι) : stepLaw P i (unfoldR R f) u=stepLaw Q (relic f i) R (u.map (relic f)):= by
    rw [paid H, paid I]; refine (bonds s (V.within _) _ _ (fun j hj=>?_)).symm
    unfold farm; apply bonds f (V.soil _); intro x hx; refine sum_congr rfl fun q _=>?_ ; rw [←V.glyph j,shoulder H V _ _ ((P.in_heat ..).2 hj),show Q.tip (s j) (f x,q)=_ from shoulder H V (x,q) j hx]; rfl

-- progress using f-prefix on entire wires. E.NonOverlap constraints must be announced
-- and off mem hEntropy.HPad; usable at coil price in cp6 main.

variable (he : Set.InjOn f {i|0<o i})(h : Lease P o)
include H V I he h
lemma threads : Balance (fun j d=> 2*blank X H.prices j d) P o (price P-unfoldR (price Q) f):=by
    let R:= price P; let S:= unfoldR (price Q) f; refine ⟨h, ?_, ?_, ?_⟩
    · rw [Pi.sub_apply,unfoldR,List.map_nil,zero_part H,zero_part I]; simp
    · intro j d u hu; unfold nth; rw [Pi.sub_apply,map_sub]; refine (abs_sub ..).trans ((add_le_add (coupon H.prices H j d j le_rfl hu) (coupon H.prices I j d j le_rfl ?_)).trans_eq (by ring)); exact (List.length_map _).le.trans hu
    intro i u hU; rw [subtracting,task_sub, settled P H, toll H I V, settled Q I]; unfold taskBill; apply congr_arg₂ (·-·) rfl; rw [due_covered H V]; congr 1; refine congr_arg₂ (·-·) (wing_cover (price Q) i ?_) (congrArg (· • (unfoldR (price Q) f u)) (tilt_covered H V i)); intro j hj hp
    refine he (lt_of_lt_of_le (Nat.zero_lt_succ _) (hU i (List.mem_cons_self ..))) (lt_of_lt_of_le (Nat.zero_lt_succ _) (hU j (List.mem_cons_of_mem _ hj))) hp
omit H V I he h

-- Uniform so no discrim p price before propagation. Reusable after P installed for
-- other data. All terms independent `F`. Keep release w true partition later.
def Reel (X:Shelf G A D)(c:ℝ)(r d:ℕ): Prop:=∀ (ι J k K T Y:Type)(_ : Fintype ι)(_ : Fintype J)(_ : Fintype k)(_ : Fintype K)(_ : Fintype T)(_ : Fintype Y)(F S:Side)(P:Planet X S ι k T)(Q:Planet X F J K Y),
   P.Steady→ Q.Steady→ ∀ f s, Overset P Q f s→ ∀ o, Lease P o→ Set.InjOn f {i| 0<o i} →∀ u:Rail G ι,u.length≤ d→ ∀ n, Local o u n→∀ j≤r, |nth j (price P u)-nth j (unfoldR (price Q) f u)| ≤ c / costLamp X n
lemma charter (Y:Good X)(r d:ℕ) :∃ c:ℝ, 0≤ c ∧ Reel X c r d:=by
    choose f hf h using fun i: Fin (r+1)=> treatment X (fun j d=>2*blank X Y j d) i.val d
    refine ⟨∑ i, f i,sum_nonneg (fun i _ => hf i),fun ι J k K T Y _ _ _ _ _ _ F S P Q H h' f' s V o ho hR u hu n hY j hj=>?_⟩
    let i: Fin (r+1):= ⟨j,by omega⟩; have hy:= h i ι k T _ _ _ S P H o _ (threads H h' V hR ho) u hu n hY; rw [nth,Pi.sub_apply,map_sub] at hy; exact hy.trans (div_le_div_of_nonneg_right (single_le_sum (fun i _=>hf i) (mem_univ i)) coin_pos.le)
end YM.RGComparison.Core16.Silk
