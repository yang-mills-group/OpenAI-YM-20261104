import YM.FVA2.TurnTall
/-!
# Auxiliary signed symmetry on cap spaces. Need on mixed source
comparison before dressing D.V Uses exact high-dimensional continuation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.ArchTurn
open Filter Topology Set Function MeasureTheory MS MS.Logarithm MS.Tide
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program MS.Dock
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Arts.Spin MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color
open scoped Topology Classical ContDiff
variable {G:Gauge} (s:Signed) {m n:ℕ} (u:m≤n)
-- lift arbitrary full signs. δC compatible using zero horizon proof.
def sky (n:ℕ) : Arts.L n ≃ Arts.L n:= let E:= equivS (Nat.zero_le n); E.symm.trans ((Equiv.sumCongr s.perm (Equiv.refl _)).trans E)
@[simp] lemma pref (i:Axis): sky s n (chair n i)= chair n (s.perm i):= by let E:= equivS (Nat.zero_le n); unfold sky; change E (Equiv.sumCongr _ _ ( E.symm (E (.inl i)) )) = E (.inl _); rw [Equiv.symm_apply_apply]; rfl
@[simp] lemma posf (i: Apart 0 n): sky s n (aside (Nat.zero_le n) i)= aside (Nat.zero_le n) i:= by let E:= equivS (Nat.zero_le n); unfold sky; change E (Equiv.sumCongr _ _ ( E.symm (E (.inr i)) )) = E (.inr i); rw [Equiv.symm_apply_apply]; rfl
def sig (n:ℕ)(i:L n): ℝ:= (arcS n s).profile i (sky s n i)
lemma tape_i (i:Axis) : sig s n (chair n i)= cross (s.flip i) true:= by apply Complex.ofReal_injective; simp only [sig,pref,arcS,crane,chair, ray_taller (Nat.zero_le n),Outlook.hand_s s i (s.perm i)]; cases s.flip i <;> simp
lemma tape_j (j:Apart 0 n) : sig s n (aside (Nat.zero_le n) j)=1:= by rw [sig,posf,profile,arcS,crane,← send_spray,arch_identity,send_spray,spray,Pi.single_eq_same] -- maybe infinite
private lemma handspr (j: Axis): (hand s).turn (spray j)= (cross (s.flip j) true :ℝ) • spray ( s.perm j ):= by
    ext t; apply Complex.ofReal_injective; rw [show (hand s).turn _ _ =_ from rfl]; change ((hand s).profile j t:ℂ)=_; rw [Outlook.hand_s s j t]; cases s.flip j <;> by_cases he:t=s.perm j <;> simp [spray,he,eq_comm]
lemma high_local (i:L n) : (arcS n s).turn (spray i)= sig s n i • spray (sky s n i) := by
   rcases Arts.rangeA i (Nat.zero_le n) with ⟨v,rfl⟩|⟨v,rfl⟩;
   · change (arcS n s).turn (spray (chair n v))= _; rw [pref s v,tape_i s v]; unfold arcS crane chair; rw [← send_spray,arch_on,handspr,map_smul,send_spray ]
   rw [ posf,tape_j ]; unfold arcS crane; rw [ one_smul,← send_spray,arch_identity ]
lemma frames (i j:L n): (arcS n s).profile i j= if sky s n i=j then sig s n i else 0:= by unfold profile; rw [high_local ]; simp only [spray, Pi.smul_apply,Pi.single_apply, smul_eq_mul,mul_ite,mul_one,mul_zero]; simp only [eq_comm]
-- sign^-2 =1, lap origin.L
lemma tape_s (i:L n): sig s n i*sig s n i=1:= by rcases rangeA i (Nat.zero_le n) with ⟨v,rfl⟩ | ⟨v,rfl⟩; change sig s n ( chair n v ) * sig s n (chair n v)=1; rw [tape_i, Koszul.cross_cross ]; simp only [tape_j,one_mul]
def remote (i:Cfield G n): Cfield G n:= (((i.1.1.map (sky s n)), i.1.2), i.2)
def bite0 (i:Cfield G n): ℂ:= match i.1.1 with
    | some x=>sig s n x
    | none=>1
lemma b_real (i:Cfield G n) : star (bite0 s i)=bite0 s i:= by unfold bite0; split <;> simp
def remode (i:Shore G n): Shore G n:= (remote s i.1,(arcS n s).turn i.2)
def stem {R:Type}(p: Legs (Mode (Cfield G n) R)): ℂ:= (p.map (bite0 s ∘ Prod.fst)).prod
@[simp] lemma stem_r {R:Type}(i:Mode (Cfield G n) R)(p: Legs (Mode (Cfield G n) R)): stem s (i::p)= bite0 s i.1*stem s p:= by unfold stem; simp
@[simp] lemma stem_append {R:Type}(l r: Legs (Mode (Cfield G n) R)): stem s (l++r)=stem s l*stem s r:=by unfold stem; simp
lemma stem_real {R:Type}(p:Legs (Mode (Cfield G n) R)) : star (stem s p)=stem s p:=by induction p with| nil=> simp [stem]| cons i l ih=> rw [stem_r,star_mul',b_real,ih]
lemma sprint (F:Rack G n) (l:Legs (Shore G n)) : whorl n s F l= stem s l * F (l.map (remode s)):= by
    let C:= arcS n s; induction l generalizing F with
    | nil=> change (flagS C G).beam F []=_; simp [ stem ]; -- pilot
    | cons i l ih=>
       unfold whorl flagS at *; obtain ⟨⟨⟨_|k,b⟩,c⟩,p⟩:=i
       · rw [fromG,ih]; exact Eq.symm (congr_arg (· * _) (one_mul _)) -- lhs weight ?
       change (leggo _ (arcS n s)).beam F ((vleg b k c,p)::l)=_; rw [cols (high_local s k), ih,stem_r,mul_assoc ]; rfl
lemma rush (F: Mob G) {n:ℕ}(l:Legs (Shore G n)) : canto s F n l=stem s l * F n (l.map (remode s)):= sprint ..
lemma cooked (p:Cfield G n): Landau.parity (remote s p) = Landau.parity p:= by rcases p with ⟨⟨_|k,_|_⟩,c⟩ <;> rfl
lemma guage (p:Cfield G n): ghostNo (remote s p)=ghostNo p:= by rcases p with ⟨⟨_|k,_|_⟩,c⟩ <;> rfl
lemma hue_spin (x:G.El)(K: Arts.Spin (Arts.L n))(F:Rack G n) : repeatC x ((flagS K G).beam F)= (flagS K G).beam ( repeatC x F ):= by
   let V:= flagS K G; ext l; induction l generalizing F with
   | nil=> simp
   | cons a l ih=>
      obtain ⟨⟨i,u⟩,p⟩:=a; rw [ repeat_cons ]; unfold flagS at *; rw [chore]; have he t: D (setLeg ((i,u),p) t) ((leggo G.ColorIndex K).beam F)= ∑ j: Atom (Arts.L n), K.rayS i j • (leggo G.ColorIndex K).beam (D ( (j,t),K.turn p ) F):= funext fun l=> by rw [Finset.sum_apply]; exact chore ..
      simp_rw [ he, c_prefix, map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,ih,smul_eq_mul, Finset.mul_sum ]; rw [Finset.sum_comm]; simp_rw [mul_left_comm (wc x _ _) (K.rayS i _)]
lemma cap_c {K:Mob G}{r:ℤ} (he:Issue r K) : Issue r (canto s K):= by
   intro n l hl; rw [rush, he n _ (by simpa only [List.length_map] using hl), mul_zero]
lemma collar_c {K:Mob G}{r:ℤ}(he:Collar r K) : Collar r (canto s K):= by
   refine ⟨?_, fun i k=> Eq.trans (hue_spin k (arcS i s) (K i)) (congr_arg _ (he.color i k)), ?_⟩
   · intro i l p q r; simp only [rush,List.map_append,List.map_cons, he.sym i (l.map ( remode s )) (remode s p) (remode s q) (r.map _), stem_append, stem_r]; unfold field remode; simp_rw [cooked]; ring -- loop?
   intro n l hl; rw [rush,he.ghost n _ ?_,mul_zero]; simp_rw [chargeInt,List.map_map,comp_def,remode,guage]; exact hl -- ghost congr
lemma invert {K:Mob G}(he:Sight K): Sight (canto s K):= by
   intro n w; rw [rush,rush,star_mul',stem_real]; have hy: (invertMom w).map ( remode s )=invertMom (w.map ( remode s )):= by unfold invertMom; simp only [List.map_map]; congr! 1; funext i; exact Prod.ext rfl (map_neg _ _)
   rw [hy,he]; unfold stem invertMom; rw [List.map_map]; rfl
lemma kForm {K:Mob G}(he:Sturdy true K): canto s K=K:= funext fun n=> he.turn n _ (fun h=>Bool.noConfusion h) -- proof arg? (True_false not)
-- costs
variable {E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
private def hop (p:Touch G n E): Touch G n E:= p.map (fun i=> (remote s i.1, (arcS n s).turn.toContinuousLinearMap ∘L i.2))
private lemma hems (p:Touch G n E)(F:Mob G)(x:E): fieldVal ((canto s F) n) p x= stem s p * fieldVal (F n) (hop s p) x:= by unfold fieldVal; rw [rush]; unfold sail; simp only [hop,stem,List.map_map]; rfl
lemma fells {z: UScale I} {a:I→ℝ}{f:I→Mob G}(he:fell z a f) : fell z a (fun i=>canto s (f i)) := by intro i E _ _ _ p; simp_rw [funext (hems s p (f _))]; exact (he i E (hop s p)).L ((ContinuousLinearMap.mul ℝ ℂ) ( stem s p )) -- new
lemma wholesome {D:Set ℂ}{f: Coat G}(he:Hol D f) : Hol D (fun i=> canto s (f i)):= ⟨ fun c R hQ hZ=> fells s (he.price c R hQ hZ), fun i z=> by simp_rw [rush]; exact fun p hp=>(he.top _ _ p hp).const_mul _ ⟩
lemma limb {f:Coat G}{F:Mob G}(hp:Shine.Lift f F): Shine.Lift (fun p=>canto s (f p)) (canto s F):= by obtain ⟨g,R,hr,h,H,rfl⟩:=hp; exact ⟨_,R,hr, wholesome s h,H.mono (fun i hi=> congr_arg _ hi), rfl⟩
lemma vibrant {f:Coat G}(hp:Shine.mer f): Shine.mer (fun p=>canto s (f p)):= by obtain ⟨n,p,H⟩:= hp; exact ⟨n,_,Shine.Lift.congr (limb s H) (Eventually.of_forall fun i=> map_smul (canto s) (i^n) (f i))⟩
lemma pole_cap {t r:ℤ}{f:Coat G}(he:Cap0 false t r f): Cap0 false t r (fun p=>canto s (f p)) := ⟨ ⟨ ⟨vibrant s he.fine.tune.mer, he.fine.tune.dice.mono (fun _ h=> sturdy_s s _ h) ⟩, he.fine.ghost.mono (fun _ h=> collar_c s h), (show realAlong _ _ from Eventually.mono he.fine.sense (fun _ h=> invert s h)) ⟩, he.cap.mono (fun _ h=> cap_c s h) ⟩
end YM.FVA2.ArchTurn
