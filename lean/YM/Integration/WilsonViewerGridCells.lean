import YM.Integration.WilsonViewerAlignedPublic

/-! The physical cutoff uses the true joint cell weights, including reflected
and nonproduct tests. An address is chosen in the cover before the native
embedding to the original ultraviolet torus. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerGridPins
open Function Filter Set MeasureTheory Extraction Table Lattice Spec PhysicalNext.Repeat.Legato
open WilsonPositionPhysicalCellTest
open private integrate from YM.Integration.WilsonPositionPhysicalCellTest
open scoped Topology Classical BigOperators
variable {G:Gauge} {R:Run G} {n:ℕ} (d:Caps n) (φ:Test n) (r:ℝ)
    (s N per:ℕ) (pick:Sites R (s,per) n→Fin n → Cover)
    (Y:(ℕ×ℕ)→R.family.book.Vector d)

theorem embedded (live:s≤N) (u:Sites R (s,per) n) :
    atCut (R:=R) d s (pick u) Y (N,per)=
      R.family.ensemble (N:=N) (p:=per) d (fun i=>(R.family.S.toDepth live per).embed (wrap _ (pick u i)))
        (Y (N,per)):=by
  simp only [atCut,Cells.location,dif_pos live]

/-- Each regular and hard comparison is tested at the literal source site.
This equality performs the joint sum only after those sites have been fixed. -/
theorem cells :
    (φ.applyTo fun x=>atCut (R:=R) d s (pick (site (R:=R) r (s,per) x)) Y (N,per))=
      ∑ u:Sites R (s,per) n,mass (R:=R) φ r (s,per) u*atCut (R:=R) d s (pick u) Y (N,per):=by
  unfold Test.applyTo
  rw [integrate (R:=R) r (s,per) (fun u x=>φ x*atCut (R:=R) d s (pick u) Y (N,per))
    (fun _=>(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const _)]
  exact Finset.sum_congr rfl fun u _=>integral_mul_const _ _

theorem variation (bank:Sites R (s,per) n→ℂ) (price:ℝ) (hp:0≤price)
    (signed:∀ u, mass (R:=R) φ r (s,per) u≠0 →
      ‖atCut (R:=R) d s (pick u) Y (N,per)-bank u‖≤price) :
    ‖(φ.applyTo fun x=>atCut (R:=R) d s (pick (site (R:=R) r (s,per) x)) Y (N,per))-
      ∑u,mass (R:=R) φ r (s,per) u*bank u‖≤(∫x,‖φ x‖)*price:=by
  rw [cells,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u,‖mass (R:=R) φ r (s,per) u*atCut (R:=R) d s (pick u) Y (N,per)-
        mass (R:=R) φ r (s,per) u*bank u‖:=norm_sum_le ..
    _ ≤ ∑u,‖mass (R:=R) φ r (s,per) u‖*price:=by
      apply Finset.sum_le_sum
      intro u _
      rw [←mul_sub,norm_mul]
      by_cases absent:mass (R:=R) φ r (s,per) u=0
      · simp [absent]
      · exact mul_le_mul_of_nonneg_left (signed u absent) (norm_nonneg _)
    _ = _ * price:=Finset.sum_mul .. |>.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonPositionPhysicalCellTest.total_variation (R:=R) φ r (s,per)) hp

end YM.Integration.WilsonViewerGridPins
end
