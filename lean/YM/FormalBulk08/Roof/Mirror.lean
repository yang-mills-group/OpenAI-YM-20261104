import YM.FormalBulk08.Roof.Enroll

/-! Signed harmony with label matrices, iterated; all variables real polynomial antecedents. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J: Type*}{G:Gauge}{d m l e r D j t :ℕ}{K:KernelChoices}{F:Frame G d}{Y:Plaza F D}{o:Loc G 1}
lemma Wade_yawn (s: Signed)(Y:Plaza F D)(h:∀ i,Wade o (Y i) d)(j:Letter F): Wade o (larch Y (lariat F s) j) d:= wadeCrow o _ _ (fun i _=> (h i).launch _)
-- rank tolerance d convenient (basis not larger). frame varies.
def Harmonized (F:Frame G d) (s:Signed)(Y: Plaza F D): Prop := ∀ i, Son (larch Y (lariat F s) i) (Y i) d s
lemma son_larch {I :Type*}[Fintype I](o:Loc G 1)(Y Z:I→Anthem D G)(s:Signed)(P: Matrix I J Pence)(h:∀ i,Wade o (Y i) d)(hZ:∀ i, Wade o (Z i) d)(hp:∀ i,Son (Y i) (Z i) d s)(j:J) : Son (larch Y P j) (larch Z P j) d s:= by
   let U(k:I):= launch (P k j) (Y k); let V(k:I):= launch (P k j) (Z k)
   have H(S:Finset I): Son (∑ i∈S,U i) (∑ i∈S,V i) d s:= by
      induction S using Finset.induction with
      | empty=> simp only [Finset.sum_empty]; exact son_zero
      | insert i S he ih=>
         rw [Finset.sum_insert he,Finset.sum_insert he]; exact ((hp i).launch _ (h i) (hZ i)).add ih ((h i).launch _) ((hZ i).launch _) (wadeCrow o _ U (fun j _=> (h j).launch _)) (wadeCrow o _ V (fun j _=> (hZ j).launch _))
   exact H _
lemma harmony_top (s:Signed)(o: Loc G 1)(F:Frame G d)(T: SectionData F)(H:Hol G)(h:T.Sound H)(hr:Bid.pop T)(hp:d+1≤D) : Harmonized F s (sectionY T hp):= by
    let Y:= sectionY T hp; have ht i:= (topC o F T H h hr hp).officers i
    intro x; refine son_round ?_ (Wade_yawn (F:=F) s Y (fun i=> (ht i).fare.through (slotsFits F i)) x) (ht x).fare ((ht x).fare.through (slotsFits F x)) (Harmony T H h hr s x hp o); change Wade o (larch Y _ _) (slots F x)
    have hx i: Clef o (larch Y (lariat F s) i) (slots F i):= by
       refine larch_cleared (Y:=Y) (T:=lariat F s) (slots F) (slots F) ?_ (fun i=> ht i) i
       intro i j k hk; unfold lariat; rw [if_neg (show ¬Crew F s i j from fun he=>by have h:= (crew_rank F s he).1;omega),map_zero]
    exact (hx x).fare
lemma reflected (H:Hol G)(F:Frame G d)(s:Signed)(Y: Plaza F D)(he:∀ i,Clef o (Y i) d)(hp:Harmonized F s Y): pantry F Y*lariat F s=lariat F s*pantry F Y:= by
   have ht i: Clef o (larch Y (lariat F s) i) d := Clef.sum Finset.univ _ (fun j _=>(he j).launch _)
   rw [← pantry_handle F _ (fun i=> (he i).fare)]; ext1 i j; exact hear_turn F s H (hp j) (ht j) (he j) i -- transposed? mulVec
variable (F)(ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W: Pot G)
variable (Y:Plaza F D)
lemma circulate (s:Signed)(o:Loc G 1)(he:Story W (pink K.penalty P.wing))(hs:LocalRatio ρ)(ht:4≤t)(hb:Harmonized F s Y)(hz:∀ i,Clef o (Y i) d): Harmonized F s (migrates a P V K W ρ h hL d d ∘ Y):= by
   let q:= lariat F s; let R:= Roof.reborn a P V K W ρ h
   have hp : q.map R=q:= by
       ext1 i j; unfold q; change R _=_; unfold lariat; unfold R; split; rw [rele,subst_C]; rfl
       rw [map_zero]
   intro i; change Son (larch _ q i) _ _ _; nth_rw 1 [←hp]; rw [←hammers ρ a P V h hL W o d d Y q (fun i=> (hz i).fare) he ht hs]; let U := larch Y (lariat F s) i; have hQ : Wade o U d:= Wade_yawn s Y (fun j=> (hz j).fare) _; let T:=Y i
   exact (son_step o P V U T W ρ h hQ he hs hL ht (hz i).fare s (hb i) d).stirs (quick_Wade o P V U W _ h hQ he hs hL ht le_rfl _) (quick_Wade o P V T W _ h (hz i).fare he hs hL ht le_rfl _) (book_equal _)
lemma breadth (he:Story W (pink K.penalty P.wing))(ht: LocalRatio ρ)(hp:4≤ t)(hr:d<D)(hd:d≤j)(H:Hol G)(s:Signed)(hy:Court o F Y)(hU:Harmonized F s Y):
   let T:=pTrain F ρ a P V h hL W Y; let Z:=lariat F s; T*Z=Z*T ∧ T⁻¹ * Z=Z*T⁻¹ ∧ Harmonized F s (avenue F ρ a P V h hL W Y):= by
    intro T Z; let U : Plaza F D:=migrates a P V K W ρ h hL d d ∘ Y; have hC i: Clef o (U i) d:=migrate_w a h hL _ (clef_through (hy.officers i) (slotsFits F i)) he hp ht le_rfl
    have hG:=performed o F Y ρ a P V h hL W H hr hd hp he ht hy; have hv:Harmonized F s U:= circulate F ρ a P V h hL W Y s o he ht hp hU (fun i=> clef_through (hy.officers i) (slotsFits F i))
    have hP : T*Z=Z*T:= reflected H F s U hC hv
    have hh:= Matrix.mul_nonsing_inv T hG.det; have hx:=Matrix.nonsing_inv_mul T hG.det; have hV:T⁻¹*Z= Z*T⁻¹:=by
       calc T⁻¹ * Z = (T⁻¹ * Z)*(T*T⁻¹) := by rw [hh,mul_one]
            _ = T⁻¹*(Z*T)*T⁻¹ := by simp [mul_assoc]
            _ = _ := by rw [←hP,← mul_assoc,hx,one_mul]
    refine ⟨hP,hV,fun i=>?_⟩; unfold avenue; change Son (larch (larch U T⁻¹) Z i) (larch U T⁻¹ i) d s; rw [larch_circuit,hV,← larch_circuit]; exact son_larch o (larch U Z) U s T⁻¹ (fun i=> Wade_yawn s U (fun j=>(hC j).fare) _) (fun i=>(hC i).fare) hv i
end YM.FormalBulk08.Roof
