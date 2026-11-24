import YM.Integration.WilsonMovingReportLedger
import YM.Integration.WilsonReportEarlySmearing

/-! Read the regulated microscopic joint moment at the very anchors used
by the genuine earlier flag event, in its original physical coordinates. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportAnchoredReading
open Filter Set Function Lattice Wilson Extraction Spec Multi RG17 OPE.Strobe
open FullVolume Table PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  {F : Final R.family f S} {n : ℕ}

/-- The fine lattice address of this particular coarse anchored physical point. -/
def raised (S : Schedule) {k N : ℕ} (cut : k ≤ N) (p : ℕ) (z : Positions n) : Positions n :=
  fun j=>(S.toDepth cut p).count.val • z j

theorem position (S : Schedule) {k N : ℕ} (cut : k ≤ N) (p : ℕ) (z : Positions n) :
    tag (S.a N) (raised S cut p z)=tag (S.a k) z := by
  ext j a
  change S.a N*(((S.toDepth cut p).count.val • z j) a : ℤ) = S.a k*(z j a : ℝ)
  rw [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←S.embeds_scale (S.toDepth cut p)]
  ring

theorem rescale (b : ℝ) {r : ℝ} (hr : 0 < r) (z : Positions n) :
    r • tag (b/r) z=tag b z := by
  ext j a
  change r*((b/r)*(z j a : ℝ))=b*(z j a : ℝ)
  field_simp

theorem original (hG : G.Simple) (L : Layout F) (r : ℝ) (d : Caps n) (w : R.family.book.Vector d)
    (ref : ∀ j,R.family.ref (d j) ≤ L.level r) (k : ℕ) (z : Positions n)
    (sep : tag (R.family.S.a k) z∈conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in L.lens,∀ cut : k ≤ i.1,
      ‖moment (n:=R.family.side i.1 i.2) (R.family.beta i.1 i.2)
          (fun U=>∏ j,WilsonReportRegularMoments.fine L d w r (p:=i.2) cut (wrap (R.family.side k i.2) ∘ z) j U) -
        S.classMoment S d (tag (R.family.S.a k) z) (fun j=>master L (d j) r (w j))‖ < ε := by
  let A : Set (Points n) := {tag (R.family.S.a k) z}
  have small : A ⊆ conf n := singleton_subset_iff.mpr sep
  have read := WilsonMovingReportLedger.original R hG L r d w ref A isCompact_singleton small ε he
  filter_upwards [read] with i true cut
  let y := raised R.family.S cut i.2 z
  have loc : tag (R.family.S.a i.1) y=tag (R.family.S.a k) z := position _ cut _ z
  have bill := true y (loc ▸ (mem_singleton _))
  rw [loc,dist_eq_norm] at bill
  have site :
      moment (n:=R.family.side i.1 i.2) (R.family.beta i.1 i.2)
        (fun U=>∏ j,WilsonReportRegularMoments.fine L d w r (p:=i.2) cut (wrap (R.family.side k i.2) ∘ z) j U) =
      R.family.numeric i.1 i.2 (fun j=>⟨d j,RG17.atRef L (d j) r i (w j)⟩) (wrap _ ∘ y) := by
    change moment (n:=R.family.side i.1 i.2) (R.family.beta i.1 i.2) _ = moment (R.family.beta i.1 i.2) _
    congr 1
    funext U
    apply Finset.prod_congr rfl
    intro j _
    change R.family.O i.1 i.2 _ ((R.family.S.toDepth cut i.2).embed (wrap _ (z j))) U =
      R.family.O i.1 i.2 _ (wrap _ (y j)) U
    rw [Ratio.embed_wrap]
    rfl
  rw [site]
  exact bill

end YM.Integration.WilsonReportAnchoredReading
end

