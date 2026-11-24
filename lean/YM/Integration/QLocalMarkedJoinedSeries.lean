import YM.Integration.QLocalMarkedJoinedCofactor

/-! The same half-open packet bijection carries summability from the old
signed field and its genuine insertion directly to the joined array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedSeries
open Function Set Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open ActualWilsonTaylorPackets ActualWilsonTaylorSlot QLocalMarkedJoinedCofactor
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

private local instance : IsTopologicalSemiring (Poly Γ) := ⟨⟩

def input (v f:ℕ→Poly Γ) (U:Config G n) (p:ℕ×Finset ℕ) :=
  f p.1 * QLocalMarkedJoinedCofactor.packet W v p.2 U

def output (K:Guard.Keeper W.p W.activities) (v f:ℕ→Poly Γ) (U:Config G n) (p:ℕ×Finset ℕ) :=
  placed (Y:=Y) K v f U p.1 * coat W v p.1 p.2 U

theorem moved {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} (K:Guard.Keeper W.p W.activities) (v f:ℕ→Poly Γ) (U:Config G n)
    (hot:∀r,f r≠0→¬Healthy W.p.threshold (Y r) U) :
    (∑' p,output (Y:=Y) K v f U p)=(∑' p,input (W:=W) v f U p) ∧
      (Summable (output (Y:=Y) K v f U) ↔ Summable (input (W:=W) v f U)) := by
  let a:=input (W:=W) v f U
  let b:=output (Y:=Y) K v f U
  have ha:Function.support a ⊆ range (Subtype.val : Roots W Y→ℕ×Finset ℕ):=
    fun p hp=>⟨⟨p,origin v f U hot p hp⟩,rfl⟩
  have hb:Function.support b ⊆ range (place (Y:=Y) K):=fun p hp=>target K v f p U hp
  have value (p:Roots W Y):b (place K p)=a p.1:=(reindex K v f p U).symm
  have sa:Summable (a ∘ (Subtype.val : Roots W Y→ℕ×Finset ℕ)) ↔ Summable a:=
    Subtype.val_injective.summable_iff (fun x hx=>not_not.mp (fun h=>hx (ha h)))
  have sb:Summable (b ∘ place (Y:=Y) K) ↔ Summable b:=(place (Y:=Y) K).injective.summable_iff (fun x hx=>not_not.mp (fun h=>hx (hb h)))
  constructor
  · exact ((place (Y:=Y) K).injective.tsum_eq hb).symm.trans
      ((tsum_congr value).trans ((Subtype.val_injective : Injective (Subtype.val : Roots W Y→_)).tsum_eq ha))
  · exact ⟨fun h=>sa.mp ((sb.mpr h).congr value),fun h=>sb.mp ((sa.mpr h).congr (fun p=>(value p).symm))⟩

theorem relative (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (f:ℕ→Poly Γ) (U:Config G n)
    (hot:∀r,f r≠0→¬Healthy W.p.threshold (Y r) U) (hf:Summable f)
    (paid:Summable (input (W:=W) (fun i=>a.each i U) f U)) (old:Summable (fun b=>a.packet b U)) :
    Summable (output (Y:=Y) K (fun i=>a.each i U) f U) ∧
      (∑' p,output (Y:=Y) K (fun i=>a.each i U) f U p)=(∑' r,f r)*a.cluster U := by
  have own:=moved K (fun i=>a.each i U) f U hot
  refine ⟨own.2.mpr paid,own.1.trans ?_⟩
  have single (b : Finset ℕ) : QLocalMarkedJoinedCofactor.packet W (fun i=>a.each i U) b U=a.packet b U := by
    by_cases h : W.activities.admissible W.p U b <;> simp [QLocalMarkedJoinedCofactor.packet,Bands.packet,h]
  have inner (r : ℕ) : (∑' b : Finset ℕ,input (W:=W) (fun i=>a.each i U) f U (r,b))=f r*a.cluster U := by
    calc
      _=∑' b : Finset ℕ,f r*a.packet b U := tsum_congr (fun b=>congrArg (f r * ·) (single b))
      _=f r*(∑' b : Finset ℕ,a.packet b U) := old.tsum_mul_left (f r)
  exact paid.tsum_prod.trans ((tsum_congr inner).trans (hf.tsum_mul_right (a.cluster U)))

end YM.Integration.QLocalMarkedJoinedSeries
