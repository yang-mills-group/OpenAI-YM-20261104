import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableLabels
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PhysicalTableUnit
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) {n : ℕ}

theorem first (s : Viewers F) (v : Fin n → S.Tag) {x : YM.Points (n+1)}
    (hx : x ∈ conf (n+1)) (d : ℕ) :
    S.useAt (spectator F s) x (Fin.cons ⟨d,S.unit d⟩ v) = S.useAt (spectator F s) (YM.Points.tail x) v := by
  let w : Fin n → C.book.Token := fun i => ⟨(v i).1,S.representative _ (v i).2⟩
  let raw : Fin (n+1) → C.book.Token := Fin.cons (C.book.one d) w
  have he (i) : S.classTokens (w i) = v i := by
    change Sigma.mk (v i).1 (S.project _ (S.representative _ _)) = v i
    rw [S.rep]
  rw [show (Fin.cons (α := fun _ => S.Tag) ⟨d,S.unit d⟩ v) = S.classTokens ∘ raw by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [raw,Function.comp_apply,Fin.cons_zero]
      rfl
    · simp only [raw,Function.comp_apply,Fin.cons_succ,he],
    S.at_project (spectator F s) (spectate F s).laws.toSymmetric (spectate_respects F s) hx,
    (spectate F s).laws.unital hx d w]
  rfl

theorem remove (s : Viewers F) (v : Fin (n+1) → S.Tag) (x : YM.Points (n+1))
    (hx : x ∈ conf (n+1)) (k : Fin (n+1)) (hk : S.pin (v k).1 (v k).2 = S.pin 4 (S.unit 4)) :
    S.useAt (spectator F s) x v =
      S.useAt (spectator F s) (WithLp.toLp 2 (x.ofLp ∘ k.succAbove)) (v ∘ k.succAbove) := by
  let p := (finSuccEquiv n).trans (finSuccEquiv' k).symm
  have p0 : p 0 = k := by simp [p]
  have pS (j : Fin n) : p j.succ = k.succAbove j := by simp [p]
  have unit : (v k).2 = S.unit (v k).1 := by
    apply S.pin_inj (v k).1
    exact hk.trans (F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric (spectate_ready F none) F.room.kernel.laws)
  have head : v k = (⟨(v k).1,S.unit (v k).1⟩ : S.Tag) := by
    rw [←unit]
  have inputs : v ∘ p = Fin.cons (α := fun _ => S.Tag) ⟨(v k).1,S.unit (v k).1⟩ (v ∘ k.succAbove) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Function.comp_apply,Fin.cons_zero,p0] using head
    · simp only [Function.comp_apply,Fin.cons_succ,pS]
  have points : YM.Points.tail (YM.Points.rearrange p x) = WithLp.toLp 2 (x.ofLp ∘ k.succAbove) := by
    apply WithLp.ofLp_injective
    funext j
    change x.ofLp (p j.succ) = x.ofLp (k.succAbove j)
    rw [pS]
  rw [← S.class_perm (spectator F s) (spectate F s).laws.toSymmetric p hx v,inputs,
    first F s _ (YM.Points.rearrange_in p hx), points]

theorem original (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Option (hierarchy F Q).Character) (v : Fin (n+1) → (hierarchy F Q).Tag)
    (x : YangMills.Points (n+1)) (hx : x ∈ WilsonFamily.separated (n+1)) (k : Fin (n+1))
    (hk : (hierarchy F Q).toLabel (v k).1 (v k).2 = (hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour) :
    (hierarchy F Q).correlation s v x =
    (hierarchy F Q).correlation s (v ∘ k.succAbove) (WithLp.toLp 2 (x.ofLp ∘ k.succAbove)) :=
  remove F s v x hx k hk

end IssuedBridge.PhysicalTableUnit
end
