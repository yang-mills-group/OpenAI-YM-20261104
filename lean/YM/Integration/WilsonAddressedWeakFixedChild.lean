import YM.Integration.WilsonAddressedWeakPanelIngress

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFixedChild
open Function Filter Lattice Wilson RG Source RG12 Labels Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu Trace.Physical
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Corona
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerReflectedTrajectory
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {k N p d:ℕ}
local notation "Rf" => R.family

private theorem composed {n m l : Side} (A : Ratio n m) (B : Ratio m l) (C : Ratio n l)
    (x : Site n) : B.embed (A.embed x) = C.embed x := by
  have counts : A.count.val*B.count.val=C.count.val := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<n.val from n.property)
    rw [← Nat.mul_assoc,← A.exact_size,← B.exact_size,← C.exact_size]
  have hl : lift (B.embed (A.embed x)) = lift (C.embed x) := by
    rw [B.lift_embed,A.lift_embed,C.lift_embed,smul_smul,Nat.mul_comm,counts]
  simpa only [wrap_lift] using congrArg (wrap l) hl

private theorem translated {f c:Side} (a:Ratio c f) (x:Site f) (q:Site c) :
    a.parent (x+a.embed q)=a.parent x+q ∧ a.residue (x+a.embed q)=a.residue x:=by
  have re:a.assemble (a.parent x+q,a.residue x)=x+a.embed q:=by
    change a.embed (a.parent x+q)+wrap f (lift (a.residue x))=x+a.embed q
    rw [show a.embed (a.parent x+q)=a.embed (a.parent x)+a.embed q from a.root.map_add ..]
    calc _=(a.embed (a.parent x)+wrap f (lift (a.residue x)))+a.embed q:=by abel
         _=x+a.embed q:=by rw [a.unpack_at]
  have pr:a.splitSites (a.assemble (a.parent x+q,a.residue x))=(a.parent x+q,a.residue x):=a.splitSites.apply_symm_apply _
  rw [re] at pr
  exact ⟨congrArg Prod.fst pr,congrArg Prod.snd ((a.unpack _).trans pr)⟩

def slide (live:k≤N) (z:Site ((Rf).side N p)) (y:Site ((Rf).side k p)) :=
  z+((Rf).S.toDepth live p).embed (y-((Rf).S.toDepth live p).parent z)

theorem parents (live:k≤N) (z:Site ((Rf).side N p)) (y:Site ((Rf).side k p)) :
    ((Rf).S.toDepth live p).parent (slide R live z y)=y ∧
    ((Rf).S.toDepth live p).residue (slide R live z y)=((Rf).S.toDepth live p).residue z:=by
  have eq:=translated ((Rf).S.toDepth live p) z (y-((Rf).S.toDepth live p).parent z)
  refine ⟨eq.1.trans ?_,eq.2⟩;abel

theorem same_letters (live:k≤N) (z:Site ((Rf).side N p)) (y:Site ((Rf).side k p))
    (i:ℕ) (hi : k ≤ i) :
    digits R N p (slide R live z y) i=digits R N p z i:=by
  by_cases e:i+1≤N
  · let a:=(Rf).S.toDepth hi p
    let b:=((Rf).path.levels.clock.op i p).ratio
    let c:=(Rf).S.toDepth e p
    let δ:=y-((Rf).S.toDepth live p).parent z
    have eq:c.embed (b.embed (a.embed δ))=((Rf).S.toDepth live p).embed δ:=by
      rw [composed a b ((Rf).S.toDepth (hi.trans i.le_succ) p),composed _ c ((Rf).S.toDepth live p)]
    simp only [digits,dif_pos e,slide]
    change b.residue (c.parent (z+((Rf).S.toDepth live p).embed δ))=b.residue (c.parent z)
    rw [←eq,(translated c z _).1,(translated b (c.parent z) _).2]
  · simp only [digits,dif_neg e]

theorem enrolled (live:k≤N) (z:Site ((Rf).side N p)) (y:Site ((Rf).side k p))
    {D:Rail Rf} {B:ℕ→ℕ→ℝ} {V:Sight Rf d p} {r:Emblems Rf d}
    (h:Enrolled R.makes D B k N p d (digits R N p z) V r):
    Enrolled R.makes D B k N p d (digits R N p (slide R live z y)) V r:=by
  refine ⟨h.starts,h.legal,?_⟩
  intro i hi hn;rw [same_letters R live z y i hi];exact h.follows i hi hn

end YM.Integration.WilsonAddressedWeakFixedChild
end
