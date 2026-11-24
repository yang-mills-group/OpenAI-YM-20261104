import YM.SignedWilsonExpansion.Dancer.Shell
/-!
# Bigarity filtration and concrete Maxwell horizon basis. Canonical seat→rank orientation.

Use `Dframe`'s label.Crest signature. We only require limits of its coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open WilsonCoeffUV.Mer.Xa MarqueQ Stair SeatsW Commission.Gram Shell
open FVA2 FVA2.Dframe FVA2.Position Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Land MS.Local.Physical
open scoped BigOperators Topology Classical
variable {G:Gauge}{b d h t w:ℕ}{ι:Type}{l:Filter ι}
namespace Fort
-- need daylight NS
abbrev Logo (G:Gauge)(h:ℕ) : Module.Basis (Toon G h) ℂ (Sec G h):= Theater.Daylight (Press.portDeck G) h
variable (i j:Toon G h) (F:Labels.Frame G h)
lemma logo (i : Toon G h): Logo G h i=theory i := theory_sig i
lemma grade (i:Toon G h): On.sectionMap h (Logo G h i) ∈ Labels.Grade (i.size,i.grade) := by
    let a:=Arrival.Birth.theory i; have H:= Arrival.Birth.vent i; let v: Sec G i.size:=Normalize.en le_rfl a; change On.sectionMap i.size v= _ at H; rw [logo,show theory i=Normalize.up (size_le i) v from rfl,← On.raised (size_le i) v,H]; -- rw match?
    exact Press.primary i.2.2 (w:=i.size) -- rank through h by defeq
abbrev evaluate (h:ℕ)(p:ℕ×ℕ) : Module.End ℂ (Sec G h):= (bulb G h).comp (Labels.gradePart p ∘ₗ On.sectionMap h)
abbrev status (i:Toon G h): ℕ×ℕ:= (i.size,i.grade)
lemma historical (i:Toon G h)(p:ℕ×ℕ): evaluate (G:=G) h p (Logo G h i)= if status i=p then Logo G h i else 0:=by
     unfold evaluate; simp only [LinearMap.comp_apply]; split_ifs with ht; · exact (congr_arg (bulb G h) (Labels.gradePart_self _ p (ht ▸ grade i))).trans ( bulb_recovers .. )
     rw [Labels.gradePart_zero _ _ _ (Ne.symm ht) (grade i),map_zero]; -- edit
-- use own pol-coordinate (spectral) from F9.SonarQ. criterion allows not every nonsupported.I need only into evidence.
lemma stale (x:Sec G h)(s:ℕ×ℕ) (p: ∀ t:F.Index,F.grades t=s→ sonar F t x=0): evaluate (G:=G) h s x=0:=by
    let v:= On.sectionMap h x; change bulb G h (Labels.gradePart s v)=0; rw [← F.basis.sum_repr v, map_sum,Finset.sum_eq_zero ( ?_ : ∀ i∈ (Finset.univ:Finset F.Index), (Labels.gradePart s) ((F.basis.repr v) i • F.basis i)=0 ),map_zero]; intro i _; rw [map_smul]; by_cases u:F.grades i=s; · exact (p _ u) ▸ zero_smul ..
    rw [Labels.gradePart_zero _ s _ (Ne.symm u) (F.pure i),smul_zero]
lemma school (i:Toon G h)(x:Sec G h) : (Logo G h).coord i x=(Logo G h).coord i (evaluate h (status i) x):=by
    rw [← (Logo G h).sum_repr x]; simp_rw [map_sum,map_smul]; apply Finset.sum_congr rfl; intro j _; rw [historical j (status i)]; split_ifs with p; · rfl
    have hz:i≠j:=fun v=>p (congr_arg (status (G:=G) (h:=h)) v).symm; simp [Module.Basis.coord_apply,hz,Ne.symm hz]
lemma drop (x:Sec G h)(p:∀ t:F.Index,F.grades t=status i→ sonar F t x=0): (Logo G h).coord i x=0:=by
   rw [school i x,stale F _ (status i) p,map_zero]
-- Weight zero Logo scalar.
lemma zero_orig (i:Toon G h)(v:i.size=0):∃ t:ℂ, Logo G h i=t • leaf G h := by
    have hi:i.grade=0:=by have ht:= Nat.le_of_lt_succ i.2.1.isLt; change i.grade ≤ i.size at ht; omega
    obtain ⟨k,H⟩:= Labels.scalar_grade (0:ℕ) (v ▸ hi ▸ grade i); exact ⟨k, by nth_rw 1 [← bulb_recovers G h (Logo G h i)]; rw [H,map_smul]; have ht: bulb G h (Labels.unit G h)=leaf G h:=( (Stair.ladderT (G:=G) h).unit ▸ (bulb_recovers G h (leaf G h)) ); rw [ht]⟩
-- :=by rw [← (Stair.ladderT (G:=G) h).unit]; exact bulb_recovers ..  map_one
-- canonical seat. low→ horizon transfer.
lemma lift_logo (i:Toon G b)(w:b≤h): Normalize.up w (Logo G b i)= Logo G h (enroll w i):= by rw [logo,logo,lift_sig]
abbrev seated (i:Toon G h):Toon G i.size:= MS.Land.read (panel i)
lemma status_seat : status (seated i)=status i:=rfl
lemma fits_seat : (seated i).size=i.size:=rfl
lemma film : Logo G h i= Normalize.up (size_le i) (Logo G i.size (seated i)):= by rw [lift_logo]; rfl
end Fort
end YM.SignedWilsonExpansion.Dancer
