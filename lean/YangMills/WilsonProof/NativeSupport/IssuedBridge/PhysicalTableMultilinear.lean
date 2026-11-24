import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableLabels
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PhysicalTableMultilinear
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
open IssuedBridge.PhysicalTableLabels
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) {n : ℕ} (s : Viewers F) {x : YM.Points n}

def representative (a : S.Union) : S.Tag :=
  let witness := F.sector.derivatives.covered F.room.kernel.laws.toSymmetric (spectate_ready F none) a
  ⟨witness.choose,witness.choose_spec.choose⟩

theorem repPin (a : S.Union) : S.pin (representative F a).1 (representative F a).2 = a :=
  (F.sector.derivatives.covered F.room.kernel.laws.toSymmetric (spectate_ready F none) a).choose_spec.choose_spec

def value (x : YM.Points n) (v : Fin n → S.Union) :=
  S.useAt (spectator F s) x (representative F ∘ v)

theorem tagged (hx : x ∈ conf n) (v : Fin n → S.Tag) :
    value F s x (fun i => S.pin (v i).1 (v i).2) = S.useAt (spectator F s) x v :=
  sameTuple F s hx _ v (fun i => repPin F (S.pin (v i).1 (v i).2))

theorem fixedGrade (hx : x ∈ conf n) (d : ℕ) (v : Fin n → S.Field d) :
    value F s x (S.pin d ∘ v) = (S.classMoment (spectator F s) (fun _ => d) x) v :=
  tagged F s hx (fun i => ⟨d,v i⟩)

include F in
theorem commonGrade (v : Fin n → S.Union) (a b : S.Union) :
    ∃ (d : ℕ) (w : Fin n → S.Field d) (a' b' : S.Field d),
      v = S.pin d ∘ w ∧ a = S.pin d a' ∧ b = S.pin d b' := by
  let full : Fin (n+2) → S.Union := Fin.cons a (Fin.cons b v)
  obtain ⟨d,y,seen⟩ := F.sector.derivatives.joint F.room.kernel.laws.toSymmetric (spectate_ready F none) full
  refine ⟨d,fun i => y i.succ.succ,y 0,y (Fin.succ 0),?_,?_,?_⟩
  · funext i
    exact congrFun seen i.succ.succ
  · exact congrFun seen 0
  · exact congrFun seen (Fin.succ 0)

theorem updateGrade [DecidableEq (Fin n)] (d : ℕ) (w : Fin n → S.Field d) (i : Fin n) (y : S.Field d) :
    update (S.pin d ∘ w) i (S.pin d y) = S.pin d ∘ update w i y := by
  funext j
  by_cases eq : j = i
  · subst j
    simp
  · simp [eq]

noncomputable def moment (hx : x ∈ conf n) : MultilinearMap ℂ (fun _ : Fin n => S.Union) ℂ where
  toFun := value F s x
  map_update_add' v i a b := by
    obtain ⟨d,w,a',b',hv,ha,hb⟩ := commonGrade F v a b
    rw [hv,ha,hb,← map_add,updateGrade (S := S) d w i (a' + b'),updateGrade (S := S) d w i a',updateGrade (S := S) d w i b',
      fixedGrade F s hx,fixedGrade F s hx,fixedGrade F s hx]
    exact (S.classMoment (spectator F s) (fun _ => d) x).map_update_add w i a' b'
  map_update_smul' v i c a := by
    obtain ⟨d,w,a',_,hv,ha,_⟩ := commonGrade F v a a
    rw [hv,ha,← map_smul,updateGrade (S := S) d w i (c • a'),updateGrade (S := S) d w i a',fixedGrade F s hx,fixedGrade F s hx]
    exact (S.classMoment (spectator F s) (fun _ => d) x).map_update_smul w i c a'

theorem original (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Option (hierarchy F Q).Character) (n : ℕ) (x : YangMills.Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ measured : MultilinearMap ℂ (fun _ : Fin n => (hierarchy F Q).labels.carrier) ℂ,
      ∀ v : Fin n → (hierarchy F Q).Tag, (hierarchy F Q).correlation s v x =
        measured (fun i => (hierarchy F Q).toLabel (v i).1 (v i).2) := by
  refine ⟨moment F s hx, ?_⟩
  intro v
  exact (tagged F s hx v).symm

end IssuedBridge.PhysicalTableMultilinear
end
