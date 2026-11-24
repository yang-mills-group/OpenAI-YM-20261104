import YM.AlbaMS.Loft.Affair
import YM.AlbaMS.Super.Drip
import YM.AlbaMS.Super.Epsilon

/-! Scaling all such variables simultaneously. Rank before Type const forecasts. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Finset Function Polynomial
open scoped BigOperators Classical Polynomial
variable {ι κ R S : Type*} [CommRing R] [CommRing S] {ρ : ι→Bool}{σ:κ→Bool} {p:Bool}
variable (z:R)(Z:ι→R) (n : ℕ) {F G : Coil ρ R} {g : ι→ι→R} {s: Finset ι}

-- multiply arbitrary characters per word (color/canonical wave).
private def rweight (u : List ι→R)(h:∀ a b, a.Perm b → u a=u b): Module.End R (Coil ρ R) where
  toFun F:= ⟨fun l=>u l * F l, fun a l i j=>by
    change _* F _=sting _ (_* F _); rw [h (a++i::j::l) (a++j::i::l) (List.Perm.append_left _ (.swap ..)), show F (a++i::j::l)=_ from F.trusted a l i j, mul_sting]⟩
  map_add' F G:= ext _ _ fun l=> mul_add (u l) (F l) (G l)
  map_smul' r F:= ext _ _ fun l=> mul_left_comm (u l) r (F l)

def loom (z:R)(n:ℕ): Module.End R (Coil ρ R):= rweight (fun l=> z^(l.length-n)) (fun _ _ h=> by rw [h.length_eq])
def weft (Z:ι→R): Module.End R (Coil ρ R):= rweight (fun l=> (l.map Z).prod) (fun _ _ h=> (h.map Z).prod_eq)
lemma looms (l:List ι): loom z n F l=z^(l.length-n) * F l:=rfl
lemma wefts (l:List ι): weft Z F l=(l.map Z).prod * F l:=rfl
lemma Tone.loom (h:Tone p F):Tone p (Coil.loom z n F):=by intro l ht; exact h l (right_ne_zero_of_mul (a:=z^(l.length-n)) ht)
lemma Tone.weft (h:Tone p F):Tone p (Coil.weft Z F):=by intro l ht; exact h l (right_ne_zero_of_mul (a:=(l.map Z).prod) ht)
lemma weft_nil : weft Z F []=F []:=by rw [wefts];simp
lemma plainWeft (p:Bool): plane p (weft Z F)= weft Z (plane p F):= by ext l; rw [polar,wefts,wefts,polar,mul_sting]
lemma weftD (x:ι): D x (weft Z F)=Z x • weft Z (D x F):=by ext l; simp only [D_read, wefts,smul_read,List.map_cons,List.prod_cons,mul_assoc]
lemma weft_mul : weft Z (F*G)=weft Z F*weft Z G:=by
  ext l; induction l generalizing F G with
  | nil=>simp [weft_nil]
  | cons x l ih=>
    rw [← D_read,← D_read (F:=_*_), mulD, weftD, weftD Z (F:=F),weftD Z (F:=G),plainWeft, smul_mul_assoc,mul_smul_comm, mulD, map_add,smul_add]; simp only [plus_read,smul_read,ih]
lemma weft_touch {L:ι→ι→R} {r:R}(h:∀ i j, L i j*Z i*Z j=r*g i j): touch L s (weft Z F)= r • weft Z (touch g s F):=by
  simp_rw [touch_apply,map_sum,weftD, map_smul,weftD,Finset.smul_sum,smul_smul]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [← mul_assoc,h]
lemma weft_cross {L:ι→ι→R} {r:R}(h:∀ i j, L i j*Z i*Z j=r*g i j) : cross p L s (weft Z F) (weft Z G)= r • weft Z (cross p g s F G):=by
  unfold cross; rw [← weft_mul,weft_touch Z h,weft_touch Z h,weft_touch Z h,plainWeft,smul_mul_assoc,mul_smul_comm, ← weft_mul,← weft_mul]; simp_rw [map_sub,smul_sub]

def needy (n:ℕ)(F : Coil ρ R) := ∀ l, F l≠0→ n ≤ l.length
lemma wefat : loom z 0 F=weft (fun _=>z) F:=by ext l; rw [looms,wefts]; simp
lemma stride (h:needy n F): weft (fun _=>z) F= (z^n) • loom z n F:= by
  ext l; by_cases t:F l=0; · simp [t,wefts,looms]
  rw [← wefat, looms, smul_read, looms, ← mul_assoc,← pow_add, Nat.add_sub_of_le (h l t), Nat.sub_zero] -- add_sub lemma
lemma loom_power (h: z^n=0)(m:ℕ): Cap (loom z m F) (m+n):=by
  intro l hl; by_contra! hn; rw [looms] at hl; apply hl; rw [pow_eq_zero_of_le (by omega : n≤l.length-m) h,zero_mul]
lemma loom_map (J:R→+* S) : Wind ρ J (loom z n F)=loom (J z) n (Wind ρ J F):=by ext l; simp_rw [blows,seep_read,looms]; change J _=_* J _; rw [map_mul,map_pow]
lemma Wind_touch (J:R→+* S): Wind ρ J (touch g s F)=touch (fun i j=> J (g i j)) s (Wind _ J F):= seep_touch _ _ fun _ _ _=> J.map_mul ..
lemma Wind_need (J:R→+* S)(h:needy n F): needy n (Wind ρ J F):=by intro l hh; exact h l fun hu=> hh (by simp [blows,seep_read,hu])

lemma loom_change (A:ι→ κ→R)(h:Routes ρ σ A): shot s A h (loom z n F)=loom z n (shot s A h F):=by
  ext l; rw [shot_read,looms,shot_read]
  suffices ∀ (m:ℕ) (H G:Coil ρ R), (∀ a : List ι, a.length=l.length→ H a=z^(a.length+m-n)*G a) → drink s A l H=z^(l.length+m-n)*drink s A l G by
    simpa using this 0 (loom z n F) F (fun a _=> by rw [looms,Nat.add_zero])
  induction l with
  | nil=> intro m H G hg; exact hg [] rfl
  | cons i l ih=>
    intro m H G hg; rw [drink_cons,drink_cons,List.length_cons,Nat.add_right_comm,Nat.add_assoc]; refine ih (m+1) _ _ fun a ha=>?_ ; simp_rw [drip_apply,sum_read,smul_read,D_read, hg (_::a) (by simp [ha]),Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [List.length_cons,Nat.add_right_comm a.length,Nat.add_assoc,mul_left_comm] -- fix
end YM.MSBar.Bric.Coil
