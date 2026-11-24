import YM.RGComparison.Core16.Witness.Rolls
/-! # Allow additional Calendar payments to the same real construction.
Retains actual UV proof input domains. Only parameter portal. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Witness
open Function Filter Lattice Wilson RG Precision RG.Supply Push.PriceCompiler
variable {G:Gauge}
def Demandable (P: Levels G→Prop): Prop:= ∀ (s:Sheet G)(w:Rolls s)(T:Protection w)(V:Delays T), ∃ W:Delays T, DelayLe V W ∧ ∀ U:Delays T, DelayLe W U→ ∀(X:Bar U)(B:Wait X)(a: Levels G), Paid B a→ P a
lemma free_node : Demandable (fun _:Levels G=>True):= fun _ _ _ v=> ⟨v,.refl _,fun _ _ _ _ _ _=> trivial⟩
lemma both {P Q:Levels G→Prop}(hp: Demandable P)(hq: Demandable Q): Demandable (fun a=> P a ∧ Q a):=by
     intro s w T V; obtain ⟨U,h,H⟩:= hp s w T V; obtain ⟨X,k,F⟩:= hq s w T U; exact ⟨X,h.trans k,fun y hy a b u hu=>⟨H _ (k.trans hy) _ b u hu,F _ hy _ b u hu⟩⟩
end YM.RGComparison.Core16.Witness
