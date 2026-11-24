import YM.Comparison.Density.Fusing.Rates

/-!
Exact restoration; BEFORE interpreting as a comparison estimate one
needs to actually supply `Conversion` with two exponent matches and
budget the `Leftovers`. No equality outside supports or at replaced
masks imposed on unmasked germs. This combiner reconstructs the full
polynomial and proves force transportation including all nonempty
marker orders. Stating it on `Tidy` does not assume complete
`Rep.Lawful` of the result. `progress` also exports the unmarked K
validity; for sources, asks for the budgets actually used (positive
prices, exponent reserves).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Fusing
open Testing Markers Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable {L : Leftovers R X G n}

-- P.p not changed; state comparisons relative to actual budgets &
-- order wherever appropriate. A change of couplings or resets requires
-- giving RECEIPTS on both exponents, not just on leftover E.
structure Conversion (P : Rep G n) (Q : Assembly R X G n)
    (Z : Rep G n) (D : Registers R X G n) (L : Leftovers R X G n) : Prop where
  side : P.p=Z.p
  vac U : P.exponent U=Z.exponent U+∑' i,L.real.value i U
  marks x U : Q.exponent.log P.p x U=D.log P.p x U+ ∑' i,L.marked x i U

def boundAlong (P Z : Rep G n) (L : Leftovers R X G n) : Rep G n:=
    {Z with activities := Pert.Attach.attach P.activities (scenery L) P.p.threshold Z.activities}
variable [Fintype V]
def restored (P : Rep G n) (Q : Assembly R X G n) (D : Registers R X G n) (L : Leftovers R X G n) : Assembly R X G n :=
    ⟨D,fun x=> chain P.p P.activities (scenery L) (Q.arms x) (spins L x)⟩
variable {P Z : Rep G n} {Q : Assembly R X G n} {w : V→ℝ} {O : Readers V X n}
variable {D : Registers R X G n} {a c b e d m : ℝ}
variable (hw : ∀ i,0<w i) (hh : 0≤ e) (h : Tidy P w O Q a c (e+1) b) (hg : Placed P.p O L) (hp : Compensated P.p O L w (e+1) d)

omit [Fintype V] [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
private lemma measureChange : (boundAlong P Z L).exponent= Z.exponent:= rfl

include hw hh h hg hp

theorem enact (x : Cross X) (U : Config G n) (he : Conversion P Q Z D L) :
    (restored P Q D L).eval (boundAlong P Z L) x U = Q.eval P x U := by
  have hsX : 0≤e+1:= hh.trans (le_add_of_nonneg_right zero_le_one)
  have hs := real_sums hw hg hsX hp U
  have hi := poly_sums hw hg hsX hp x U
  let X:= scenery L
  obtain ⟨f,hf,hA,hQ⟩:= raw hw hsX h x; obtain ⟨g,-,hB,hT⟩:= Deposits.pay hw hsX (fun i=> hg.nonempty i) (prices hw hg hsX hp) (spins_tickets hg) x
  have hJ := hA.of_nonneg_of_le (fun i=> Poly.nonnegative hw (Q.arms x i U)) (fun i=> hQ i U); have hG:= hB.of_nonneg_of_le (fun i=> Poly.nonnegative hw (spins L x i U)) fun i=> hT i U
  have H:= Markers.gas_eq hw hJ hG (p:=P.p) (X:=scenery L) (hr:=fun _ => rfl) (hz:=fun i=> hg.empty x i U) hs hi (fun i=> (h.carries x).flagged i U) (fun i=> (escort hg x).flagged i U) Z.activities
  have h' : mist P.p (boundAlong P Z L).activities ((restored P Q D L).arms x) U=mist P.p P.activities (Q.arms x) U*magnify (∑' i,L.real.value i U) (∑' i,L.marked x i U):= H
  simp only [Assembly.eval,measureChange]
  rw [show (boundAlong P Z L).p=P.p from he.side.symm,h',he.vac,he.marks, magnify_add (baseline _ _) (by rw [Poly.share hi]; simp [hg.empty])]; dsimp only [restored]; ring

variable {y z q β : ℝ} (hq : 1≤q) (ht : 0≤ β) (hb : ((P.p.B+P.p.B+1:ℕ):ℝ)^4*β ≤ 1) (hm : q*b+d*Real.exp d ≤ β)
  (hs : P.activities.ForcedFamily P.p) (hB : Z.p=P.p) (hd : Layout P.p O D) (ha : D.Budget P.p O w y z)

include hq ht hb hm hs hB hd ha

theorem extent : Assembly.Tidy (boundAlong P Z L) w O (restored P Q D L) y z e ((Real.exp β-1)/q) := by
  let A:= boundAlong P Z L
  let N:= restored P Q D L
  have hv : A.p=P.p:= hB
  refine ⟨⟨?_,fun x=>?_,fun i U=>?_⟩,?_,?_⟩
  · change Layout A.p O D; rw [hv]; exact hd
  · change Manifest _ A.activities A.p _; rw [hv]; exact author hs (permitted hg) (h.carries x) (escort hg x) _
  · let X:= scenery L
    change Catalogue _ (ranges A.activities i) (fun x=>chain P.p P.activities X (Q.arms x) (spins L x) i U)
    unfold chain; by_cases hi : (page P.activities X i).eligible P.p.threshold U
    · simp only [if_pos hi]; refine Catalogue.prod _ _ fun j hj=> ?_; have hy : X.area P.activities j ⊆ ranges A.activities i:=fun k hk=> mem_biUnion.mpr ⟨j,hj,hk⟩
      cases j with
      | inl j=> exact (h.tickets j U).roomier hy
      | inr j=> exact (spins_tickets hg j U).roomier hy
    simp only [if_neg hi]; exact Catalogue.empty
  · change Budget A.p O D w y z; rw [hv]; exact ha
  obtain ⟨f,hf,hF,hX⟩:= h.bill
  obtain ⟨g,hg,hG,hY⟩:=prices hw hg (hh.trans (le_add_of_nonneg_right zero_le_one)) hp
  change Deposits A.p _ _ _ _ _ _; rw [hv]
  refine ⟨_,fun x hx=> tile_over _ _ _ (hf x hx) (hg x hx),fun i=> tile_carries _ _ f g hF hG _ i Z.activities,?_⟩
  rw [← add_assoc] at hX hY
  exact tile_cost hw hq ht (show ((P.p.B+P.p.B+1:ℕ):ℝ)^4*β ≤ 1 from hb) (p:=later P.p e hh) hm hX (X:=scenery L) hY Z.activities

-- Only vacuum moves asserted, not symmetry if marker placements
-- are held fixed or if given history presentation has broken the
-- marker orbits (do not infer markings from vacuum labels).
theorem progress (HG : ∀ s b, Nonempty (P.activities.Moves s b)) (hj : ∀ s b, Nonempty (Z.activities.Moves s b)) {κ:ℝ} (Hk : 0 < κ) :
    let A:= boundAlong P Z L
    A.activities.ForcedFamily A.p ∧ A.activities.KBound (later P.p e hh) ((Real.exp β-1)/q) ∧
      (∀ s b, Nonempty (A.activities.Moves s b)) ∧ Account (later P.p e hh) w O.source (ranges A.activities) (restored P Q D L).arms κ (((Real.exp β-1)/q)/κ) := by
  intro A
  have H := Fusing.extent hw hh h hg hp hq ht hb hm hs hB hd ha
  let Y := restored P Q D L
  have HE : A.p=P.p:=hB
  refine ⟨?_,?_,fun s b=> ?_,?_⟩
  · rw [HE]; exact Pert.Attach.forced hs (permitted hg)
  · let M:= later A.p e hh
    rw [← HE]; change A.activities.KBound M _
    obtain ⟨f,hf,hF,hX⟩:= H.bill
    have HX:= H.carries 0; have HM : Manifest (Y.arms 0) A.activities M O.source := ⟨⟨HX.sym,HX.borel,HX.reads,HX.bears⟩,HX.quiet,HX.flagged⟩
    apply vacuum_bound (p:=M) _ hw (w':=0) le_rfl HM
    exact ⟨f,hf 0 (fun _=>by simp), hF,by simp only [add_zero]; exact hX⟩
  · exact ⟨Pert.Attach.moving ((HG s b).some) ((hj s b).some) (((permitted hg).move s b).some)⟩
  rw [← HE]; exact H.bill.rooted hw hh Hk
end YM.Comparison.Density.Fusing
