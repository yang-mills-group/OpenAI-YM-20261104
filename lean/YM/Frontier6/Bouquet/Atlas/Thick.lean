import YM.Frontier6.Bouquet.Atlas.Interior

/-! Descendant parameter space preserving the parent widths and footprint
 chart. Outside this space the entire term can be omitted (including any cut
 on that refined patch), subject to `Contains` in the uses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier.Court
open Function Set Finset Ensemble MeasureTheory Normal Filter Audit Metric Submodule
open Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P:Ensemble}{i:P}(Z:Court i)
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
    {K:Final C F S} [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    (A: Air (S:=S) P I L Y)
def toAura (Z:Court i)(x:I)(z:Margin P Z.split): Aura Z.split:=⟨transit Z.legend.le (A.region x).center z,Z.balcony (A.region x) (A.lengths x i)⟩ -- order
local notation "Q"=> Z.split
def Love (x:I)(z:Margin P Z.split): Prop:= let u:=toAura A Z x z; ∀ i:Z.split, u.center i∈ u.foot i
abbrev Volunteers (Z:Court i) := { p : I× Margin P Z.split // Z.Love A p.1 p.2 }
def newWorld : Air (S:=S) Z.split (Z.Volunteers A) L Y:= heir A Z.legend.le (Prod.fst ∘ Subtype.val) (fun x=> toAura A Z x.val.1 x.val.2)
section
variable {A Z}
lemma atVolunteer {M:Pod→ℝ}(he: A.Welkin M){x:I}{f:Full (fiber P)} (hf:Fair f (A.region x).foot (A.region x).center)(ht:Z.Contains (A.lengths x i) f){z:Margin P Z.split}{v:fiber Z.split} (h:forward (plan_sub Z.legend.le) (insideCL loft_le z) v∈tsupport f): Z.Love A x z := fun p=> Z.enlivens (A.length_pos x i) (he.safe x) hf ht h _
lemma restrict_empty {M:Pod→ℝ}(he: A.Welkin M){x:I}{f:Full (fiber P)} (hf:Fair f (A.region x).foot (A.region x).center)(ht:Z.Contains (A.lengths x i) f){z: Margin P Z.split} (hh:¬ Z.Love A x z): restrictS (plan_sub Z.legend.le) (insideCL loft_le z) f=0:=by
   ext1 v; exact image_eq_zero_of_notMem_tsupport (fun hv=>hh (atVolunteer he hf ht (restrict_support _ _ _ hv))) -- elabor?
end
section
variable {M:Pod→ℝ}{d:Slot→ℕ}
lemma overSky (hv:A.Welkin M)(hD:Dais K d P M): Air.Welkin (Z.newWorld A) M:= by
   apply heir_welkin A Z.legend.le _ _ (M:=M) (hv) -- comma
   · exact fun i=> Z.subset _ _
   · intro p; exact Aura.cozy_move Z.legend.le p.val.2 hD (hv.safe _) (Z.subset _ _) (Z.convex _ _ (hv.safe _)) p.property
   exact fun p=> Z.placements _ (A.length_pos p.val.1 _)
lemma following (he:Air.Hosts K A) : Air.Hosts K (Z.newWorld A):=by
   apply heir_host A Z.legend.le _ _ (fun i:Z.Volunteers A=>Z.subset (A.region i.val.1) (A.lengths i.val.1 _)) Z.pos _ he
   intro p u v hp h x hx y hy; let q:= p.val.1; have hN:assign Z.legend.le u=i:= (members ..).mp (Z.focus u v hp h|>.1); rw [hN]; exact Z.crown_distance _ (A.length_pos q _) hp h hx hy
end
end YM.Frontier6.Bouquet.Atelier.Court
