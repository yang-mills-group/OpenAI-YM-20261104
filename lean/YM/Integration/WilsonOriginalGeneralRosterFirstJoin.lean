import YM.Integration.WilsonOriginalGeneralRosterFile
import YM.Integration.WilsonOriginalCovarianceDatedPassage

/-! An occupied physical product is returned to its older, signed two-block
covariance together with all intervening first joins. The four-slot specialization
keeps both two-field means, including at the pre-meeting dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterFirstJoin
open Function Finset MeasureTheory Lattice RG Wilson Source Labels OPE.Therm
open PhysicalNext.Repeat.Legato Extra.Histories Motion Marker
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonOriginalConditionalCovarianceReturn (Billed covariance)
open WilsonOriginalCovarianceDatedPassage (level joint)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n N per f K req power t:ℕ}{d:Fin n→ℕ}{fk:f≤K}{cut:K≤N}{B:ℝ}
    (A:Panel R d N per f K fk cut req power t B)
local notation "C" => R.family
local notation "μ" => scene (C).path N per N
local notation "raw" s:max => physical R d (N:=N) A.names A.turn A.loc s

def mark {k:ℕ}(s:Finset (Fin k)):(Stock.census (Fin k)).Mode:=⟨s,mem_univ _⟩

theorem billed (s:(Stock.census (Fin n)).Mode):∃b:ℝ,Billed R b (raw s):=by
  have c:Continuous (raw s):=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  obtain ⟨M,cap⟩:=(isCompact_range c.norm).bddAbove
  exact ⟨M,c.aestronglyMeasurable,fun U=>cap ⟨U,rfl⟩⟩

theorem original (s q:Finset (Fin n))(disjoint:Disjoint s q){u:ℕ}(old:u≤N):
    (∫U,(raw (mark (s∪q))) U ∂μ)=
      (∫U,(raw (mark s)) U ∂μ)*(∫U,(raw (mark q)) U ∂μ)+
        level R N (raw (mark s)) (raw (mark q)) u+
          ∑j∈range (N-u),joint R N (raw (mark s)) (raw (mark q)) (u+j):=by
  obtain ⟨_,left⟩:=billed R A (mark s)
  obtain ⟨_,right⟩:=billed R A (mark q)
  have combined:(raw (mark (s∪q)))=(fun U=>(raw (mark s)) U*(raw (mark q)) U):=by
    funext U
    exact Finset.prod_union disjoint
  have law:=WilsonOriginalCovarianceDatedPassage.original R left right (le_refl N) old
  unfold covariance at law
  rw [combined]
  linear_combination law

theorem four {D:Fin 4→ℕ}(P:Panel R D N per f K fk cut req power t B){u:ℕ}(old:u≤N):
    let fields:=fun s:Finset (Fin 4)=>physical R D (N:=N) P.names P.turn P.loc (mark s)
    (∫U,fields univ U ∂μ)=(∫U,fields {0,1} U ∂μ)*(∫U,fields {2,3} U ∂μ)+
      level R N (fields {0,1}) (fields {2,3}) u+
        ∑j∈range (N-u),joint R N (fields {0,1}) (fields {2,3}) (u+j):=by
  have split:({0,1}:Finset (Fin 4))∪{2,3}=univ:=by decide
  simpa only [split] using original R P {0,1} {2,3} (by decide) old

end YM.Integration.WilsonOriginalGeneralRosterFirstJoin
end
