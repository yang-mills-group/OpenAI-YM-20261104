import YM.Integration.WilsonMarkedIndependentPhysicalIntake
import YM.Integration.PeriodicMarkedWinding
import YM.Integration.WilsonOlderFreshConnectedRobe

/-! Dated compact words of the complete independent table, after all relative child positions
have been summed. Finite sides keep their signed winding discrepancy on this same named word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDatedVerseReprint
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Realm WilsonMarkedIndependentPhysicalIntake
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I → ℕ}{e m:ℕ}

def printed (Y:Outerm G D)(k:I → ℕ)(e:ℕ)(J:Finset I)(c:I)(y:I → Cover) :=
  shifted (baton (sphere (Y y J) (mass k J) (e+1) c y) (e+1)) (y c)

def Issued (Y:Outerm G D)(k:I → ℕ)(e:ℕ)(J:Finset I)(c:I)(y:I → Cover)(t s C A:ℝ) :=
  let paid:=sphere (Y y J) (mass k J) (e+1) c y
  Rains paid (e+1) t (C*A*Real.exp (-s/2*realmSize J y)) ∧
  tenure paid J y c (e+1) t (C*A*Real.exp (-s/4*realmSize J y)) ∧
  ∀a ≤ e,(printed Y k e J c y).2 a=(Y y J).2 a ∧
    ∀n r,(printed Y k e J c y).1 n a r=Carp.plume ((Y y J).2 a r) n

omit [DecidableEq I] in
theorem publish (Y:Outerm G D)(well:Wellness k Y){n:Side}{σ A:ℝ}(hs:0<σ)(hA:0 ≤ A)
    (paired:PairedAt e Y n σ A)(J:Finset I)(c:I)(root:c∈J):
    ∃ t C:ℝ,0<t ∧ t≤σ ∧ 0≤C ∧ ∀y,Issued Y k e J c y t σ C (A^J.card):=by
  obtain ⟨t,C,pos,small,hC,bought⟩:=planet G J.card (mass k J) (e+1) σ hs
  refine ⟨t,C,pos,small,hC,?_⟩
  intro y
  obtain ⟨rain,rent,exactJet⟩:=bought _ (Y y J) I J y c (A^J.card) (well.level' y J) root
    le_rfl (pow_nonneg hA _) (fun a ha r=>(paired y J a (Nat.le_of_lt_succ ha) r).access) (e+1) le_rfl
  exact ⟨rain,rent,fun a ha=>shineZ (Y y J) y rain pos exactJet a (Nat.lt_succ_of_le ha)⟩

omit [DecidableEq I] in
theorem price (Y:Outerm G D){n:Side}{σ A:ℝ}(hs:0<σ)(paired:PairedAt e Y n σ A)
    (J:Finset I)(c:I)(root:c∈J)(z:I → Site n){t C:ℝ}
    (filed:Issued Y k e J c (PeriodicMarkedWinding.roots n z c) t σ C (A^J.card))
    (a:ℕ)(through:a≤e)(r:ℕ)(x:Fin r → Woods G n) :
    let y:=PeriodicMarkedWinding.roots n z c
    ‖((Y y J).1 n a r x)-(printed Y k e J c y).1 n a r x‖ ≤
      (((priceM (Hooks G) r σ+tiePay (Hooks G) r (σ/4)+1)*A^J.card+A^J.card)*
        catchW (σ/32/16) n)*Real.exp (-(σ/32/2)*Syn (tor n) z J x):=by
  intro y
  rw [(filed.2.2 a through).2 n r]
  exact (norm_sub_rev _ _).le.trans ((PeriodicMarkedWinding.periodized z c root hs
    (paired y J a through r)).2 x)

theorem original (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(engineering:I → ℕ)
    {s:ℝ}(hs:0<s):
    ∃(d:ℕ)(C σ:ℝ),1 ≤ C ∧ 0<σ ∧ ∀N,m<N → ∀(n:Side)(incoming:Outerm G D),
      Wellness k incoming → ∀ V A:ℝ,1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      PairedAt e incoming (n*(loose Q.draws m).L) s A →
      let lower:=stout Q.draws Q.paid m N engineering k incoming
      let wage:=C*V^d*A
      PairedAt e lower n σ wage ∧ ∀(J:Finset I)(c:I),c∈J →
        ∃t M:ℝ,0<t ∧ t≤σ ∧ 0≤M ∧ ∀y,Issued lower k e J c y t σ M (wage^J.card):=by
  obtain ⟨d,C,σ,hC,hσ,step⟩:=posted (D:=D) (k:=k) Q hm engineering hs
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N cut n incoming well V A hV hA quiet marks lower wage
  have result:=step N cut n incoming well V A hV hA quiet marks
  have law:=Seating Q.draws Q.paid incoming Q.hG Q.green cut well engineering
  exact ⟨result,fun J c root=>publish lower law hσ (by positivity) result J c root⟩

end YM.Integration.WilsonReceivedDatedVerseReprint
