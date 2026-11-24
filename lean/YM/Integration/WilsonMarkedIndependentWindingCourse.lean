import YM.Integration.WilsonMarkedIndependentWinding
import YM.Integration.WilsonDepositedFreshFiniteHistory

/-! Cutoff-uniform price of the independently declared finite and covered histories on the original realm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentWindingCourse
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonFiniteMarkedHistoryStep
open WilsonMarkedIndependentConnectedHistory (finite cover)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

open WilsonMarkedIndependentWinding (Folded periodized)
open IndependentSourcePathFamily WilsonDepositedFreshFiniteHistory
variable [Fintype I]
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ (d:ℕ)(C σ:ℝ),1≤C ∧ 0<σ ∧ ∀N,b≤N→
    ∀(seed:Outerm G D),Wellness k seed→∀V₀ A:ℝ,1≤V₀→1≤A→
    WilsonFiniteVacuumWindingDate.positive V R.metals.O e N b s V₀ →
    paired e seed s A →
    Folded R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k seed σ (C*V₀^d*A):=by
  filter_upwards [FundedMarkedCoverRows.realm R simple v funded 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) e 0 0] with j h
  obtain ⟨Q,draws,scheme,_,anchor,_⟩:=h
  intro b live
  obtain ⟨d,C,σ,hC,hσ,step⟩:=WilsonFiniteMarkedHistory.original (D:=D) (k:=k) Q K j b anchor.le live hs
  rw [draws,scheme] at step
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N top seed well V₀ A hV hA quiet old
  exact periodized R u tags simple v funded live top K k seed well a hσ (step N top seed well V₀ A hV hA quiet old).2

variable {I₀ I₁:I→Type}[∀i,Fintype (I₀ i)][∀i,Fintype (I₁ i)]

def received (K k:I→ℕ)(N b:ℕ)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i)):Outerm G D:=
  enter old (Gears V R.metals.O K k N (b+1) b (independent X)) (independent Y)

theorem deposited (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ (d:ℕ)(C σ:ℝ),1≤C ∧ 0<σ ∧ ∀N,b<N→
    ∀V₀:ℝ,1≤V₀→WilsonFiniteVacuumWindingDate.positive V R.metals.O e N (b+1) s V₀ →
    Folded R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k (received R K k N b old X Y) σ (C*V₀^d):=by
  filter_upwards [FundedMarkedCoverRows.realm R simple v funded 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) e 0 0] with j h
  obtain ⟨Q,draws,scheme,_,anchor,_⟩:=h
  intro b live
  obtain ⟨d,C,σ,hC,hσ,step⟩:=WilsonDepositedFreshFiniteHistory.original (D:=D) (k:=k)
    Q K j b anchor.le live old X Y hX hY hs
  unfold bank at step
  rw [draws,scheme] at step
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N cut V₀ hV quiet
  have upper:Wellness k (Gears V R.metals.O K k N (b+1) b (independent X)):=
    Cog V R.metals.O cut (independent X) (OriginalCoverReanchoring.deposited X hX).1 simple R.alloy.B.ratio (Nat.le_succ _)
  have income:Wellness k (received R K k N b old X Y):=lawful old upper (OriginalCoverReanchoring.deposited Y hY).1
  exact periodized R u tags simple v funded live cut.le K k _ income a hσ (step N cut V₀ hV quiet)

/-- No upper quiet comparison is needed at the lowest retrieved coupling grade. -/
theorem leading (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ C σ:ℝ,1≤C ∧ 0<σ ∧ ∀N,b<N→
    Folded R u tags (N:=N) (b:=b) (j:=j) (e:=0) K k (received R K k N b old X Y) σ C:=by
  filter_upwards [deposited R u tags simple v funded 0 K k a old X Y hX hY hs] with j step
  intro b live
  obtain ⟨d,C,σ,hC,hσ,each⟩:=step b live
  refine ⟨C,σ,hC,hσ,?_⟩
  intro N cut
  have quiet:WilsonFiniteVacuumWindingDate.positive V R.metals.O 0 N (b+1) s 1:=by
    intro _ i pos hi
    omega
  simpa only [one_pow,mul_one] using each N cut 1 le_rfl quiet

end YM.Integration.WilsonMarkedIndependentWindingCourse
end
