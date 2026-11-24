import YM.SchemeConversionRG11.FirstW.Vane.Mirror
/-! All-image orientation of cubic and turn conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
lemma shape_pull (s : Signed) (p : Ear G (Per n)) : tbranch G n (p ∘ₗ Bare.wideLink G s)=Bare.wideLink G s⁻¹ (tbranch G n p) := by 
 rw [pips_all p,show (∑ e, pinch e (ladder p e)) ∘ₗ (Bare.wideLink G s)=∑ e,(pinch e (ladder p e) ∘ₗ (Bare.wideLink G s)) from LinearMap.ext (fun x=>by rw [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.sum_apply];rfl)]; simp_rw [map_sum,tilt_row]
private lemma cube_rule {E : Type*} [AddCommGroup E] [Module ℝ E] (L:E→ₗ[ℝ] E→ₗ[ℝ] E→ₗ[ℝ] ℝ) (A B C:E) (hl:∀x y z,L x y z=L y x z) (hr:∀x y z,L x y z=L x z y) : let b (A:E):=L A A A; (6:ℝ)*L A B C=b (A+B+C)-b (A+B)-b (A+C)-b (B+C)+b A+b B+b C := by
  dsimp only; simp only [map_add,LinearMap.add_apply,hl,hr];ring
lemma tower_datum (A B C : Wind G X) (x : Four X) (w : Walk) : let b (A : Wind G X) := tower G x w A A A; (6:ℝ) * tower G x w A B C = b (A+B+C)-b (A+B)-b (A+C)-b (B+C)+b A+b B+b C := by
  exact cube_rule (tower G x w) A B C (fun _ _ _=> tower_sym ..) (fun _ _ _=> tower_cross ..)
lemma ticket_turn (A B C : Wind G X) (s : Signed) (x : Four X) (i j:Step) :
    tower G x (icon i j) (Bare.wideLink G s A) (Bare.wideLink G s B) (Bare.wideLink G s C) = tower G (s.act x) (icon (i.rotate s) (j.rotate s)) A B C := by
  let b:= icon (i.rotate s) (j.rotate s)
  have h (A : Wind G X) : let a:= Bare.wideLink G s A; tower G x (icon i j) a a a = tower G (s.act x) b A A A := by
    dsimp only; rw [peaks,peaks]; simp only [point_pull,travel_pull (x:=x),affine,add_zero]; rw [show (icon i j).map (fun d=>d.rotate s) = b from by simp [icon,b,Step.rev_rotate]]
  apply mul_left_cancel₀ (a:=(6:ℝ)) (by norm_num)
  rw [tower_datum,tower_datum]; simp_rw [←map_add (f:=Bare.wideLink G s),h]; rfl
private def drive (s:Signed) (i:Ticket) : Ticket := (((fresh i).rotate s).dir, ((fresh i).rotate s).neg)
lemma fresh_drive (s:Signed) (i:Ticket) : fresh (drive s i)=(fresh i).rotate s := rfl -- private leaks
private lemma turn_drive (s:Signed) (i:Ticket) : drive s⁻¹ (drive s i)=i := by
  have e : fresh (drive s⁻¹ (drive s i))=fresh i:=by rw [fresh_drive,fresh_drive,Step.rotate_mul,inv_mul_cancel,Step.rotate_one]
  exact Prod.ext (congrArg Step.dir e) (congrArg Step.neg e)
def driveEq (s:Signed): Ticket≃Ticket where
 toFun := drive s
 invFun := drive s⁻¹
 left_inv := turn_drive s
 right_inv i := by simpa using turn_drive s⁻¹ i
lemma gear_push (A B C : Wind G X) (s:Signed) (x : Four X) :
    (∑ i:Ticket,∑ j:Ticket,tower G x (icon (fresh i) (fresh j)) (Bare.wideLink G s A) (Bare.wideLink G s B) (Bare.wideLink G s C)) =
    ∑ i:Ticket,∑ j:Ticket,tower G (s.act x) (icon (fresh i) (fresh j)) A B C := by
  let P (i j:Ticket):=tower G (s.act x) (icon (fresh i) (fresh j)) A B C
  simp_rw [ticket_turn,←fresh_drive]; change (∑ i:Ticket,∑ j:Ticket,P (driveEq s i) (driveEq s j))=_
  exact (Finset.sum_congr rfl fun i _=> Equiv.sum_comp (driveEq s) (P (driveEq s i))).trans (Equiv.sum_comp (driveEq s) (fun i=> ∑ j:Ticket,P i j))
private def backward : Signed := ⟨Equiv.refl _,fun _=>true⟩
lemma swallowed (A B C : FullT G n) :
    wheels (fun x w=> tower G x w (reflectT G n A) (reflectT G n B) (reflectT G n C))=wheels (fun x w=> tower G x w A B C) := by
  let t := backward
  have eh (x : Site n) : t.act x = -x := by funext i; simp [t, backward,Signed.act]
  have he (A:FullT G n) : reflectT G n A = Bare.wideLink G t A := by
    funext e; simp only [Bare.wideLink_apply,eh]; rcases e with ⟨x,i⟩; simp [t, backward, Step.rotate,posDir,Step.used,reflectT,Orb.image]
  simp_rw [he,wheels,gear_push,eh]; exact Equiv.sum_comp (Equiv.neg (Site n)) (fun x=> ∑ i:Ticket,∑ j:Ticket, tower G x (icon (fresh i) (fresh j)) A B C)
end YM.RG11.FirstW
