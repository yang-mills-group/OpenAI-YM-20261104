import YM.Integration.WilsonThermometerWeakMovedExperiment

/-! The original microscopic residue is kept inside its translated coarse cell.
The right reflection invoice is indexed by displacement from its actual
centered enrollment, while the measured two-point function uses both sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMovedCovers
open Function Set Filter Lattice RG Wilson Source Push MergeProof Cells
open PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable (S:Schedule) {k N:ℕ} (p:ℕ) (live:k≤N)
local notation "K" => S.toDepth live p

def move (z:Site (S.side N p)) (a:Site (S.side k p)):Site (S.side N p):=
  z+(K).root (a-(K).parent z)

theorem letter (z:Site (S.side N p)) (b:Cover):
    ∃q:Cover,wrap (S.side N p) q=move S p live z (wrap (S.side k p) b) ∧
      ∀j:Axis,|S.gridPoint N q j-S.gridPoint k b j|≤S.a k:=by
  let c:=lift ((K).residue z)
  let q:Cover:=(K).count.val • b+c
  refine ⟨q,?_,?_⟩
  · rw [show wrap (S.side N p) q= (K).embed (wrap _ b)+wrap _ c by dsimp only [q];rw [map_add,(K).embed_wrap]]
    have H:(K).root ((K).parent z)+wrap _ c=z:=(K).unpack_at z
    unfold move
    rw [map_sub]
    change (K).root (wrap _ b)+wrap _ c=z+((K).root (wrap _ b)-(K).root ((K).parent z))
    calc
      _=((K).root ((K).parent z)+wrap _ c)+((K).root (wrap _ b)-(K).root ((K).parent z)):=by abel
      _= _:=by rw [H]
  intro j
  have align:S.a N*(K).count.val=S.a k:=S.embeds_scale (K)
  have centered:=lift_centers ((K).residue z) j
  have small: |(c j :ℤ)| ≤ (K).count.val:=abs_le.mpr ⟨by dsimp [c];omega,by dsimp [c];omega⟩
  have cm:|(c j:ℝ)|≤(K).count.val:=by exact_mod_cast small
  have price:(q j:ℝ)=(K).count.val*(b j:ℝ)+(c j:ℝ):=by simp [q,nsmul_eq_mul]
  change |S.a N*(q j:ℝ)-S.a k*(b j:ℝ)|≤_
  rw [← align,price]
  calc
    _=S.a N*|(c j:ℝ)|:=by rw [show S.a N*((K).count.val*(b j:ℝ)+(c j:ℝ))-S.a N*(K).count.val*b j=S.a N*c j by ring,abs_mul,abs_of_pos (S.a_pos N)]
    _≤_:=mul_le_mul_of_nonneg_left cm (S.a_pos N).le

theorem displacement (z:Site (S.side N p)) (b:Cover):
    ∃q:Cover,wrap (S.side N p) q=move S p live z (wrap (S.side k p) b)-move S p live z 0 ∧
      ∀j:Axis,S.gridPoint N q j=S.gridPoint k b j:=by
  refine ⟨(K).count.val • b,?_,?_⟩
  · rw [← (K).embed_wrap];unfold move;rw [map_sub,zero_sub,map_neg];change (K).root (wrap _ b)=_;abel
  intro j
  have align:S.a N*(K).count.val=S.a k:=S.embeds_scale (K)
  change S.a N*(((K).count.val • b) j:ℝ)=S.a k*(b j:ℝ)
  rw [←align]
  simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,mul_assoc]

end YM.Integration.WilsonThermometerWeakMovedCovers
end
