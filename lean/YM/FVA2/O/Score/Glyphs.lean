import YM.FVA2.O.Score.Alphabet
/-!
# Graded alphabet transformations
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Score
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open Dframe FVA2.Scale MS.Rake MS.Theater Level
variable {G:Gauge}{I:Type}{n m d k:ℕ}
abbrev LivesP (p:Scan G n):= (i:Fin n)→ Grade G ( heft ( p i ) )
def decode (p:Scan G n)(v:LivesP p): Scan G n:= fun i=> own (v i)
variable (p:Scan G n)(q:Scan G m)
lemma total_h (v:LivesP p): totalG (decode p v)=totalG p:= rfl
abbrev foldA (p:Scan G n):= {v:Scan G n // ∀ i, heft ( v i )=heft (p i)}
lemma own_in : Injective (own (d:=d) ( G:=G )):= fun _ _ h=> eq_of_heq (( Rake.Label.mk.inj h ).2)
lemma hook {p q:Q G} (h:heft p=heft q): own ( h ▸ p.item : Grade G ( heft q ) )=p:= by cases p; cases q; dsimp only [ heft ] at h; cases h; rfl
def recode : LivesP p ≃ foldA p:={
    toFun v:= ⟨ decode p v,fun _=>rfl ⟩
    invFun v:= fun i=>( v.property i ) ▸ (v.val i).item
    left_inv x:= by funext i; rfl
    right_inv x:= Subtype.ext (funext fun i=> hook (x.property i)) }
local notation "V0"=> Fin.append p q
abbrev left0 (f:Fin (n+m)→ I): Fin n→ I:= f ∘ Fin.castAdd m
abbrev right0 (f:Fin (n+m)→ I): Fin m→ I:= f ∘ Fin.natAdd n
lemma correct (p:Scan G (n+m)): Fin.append (left0 p) (right0 (n:=n) p)=p:= by funext i; induction i using Fin.addCases <;> simp [left0,right0, Fin.append_left, Fin.append_right]
def merge : foldA p × foldA q ≃ foldA ( Fin.append p q ) :={
    toFun x:= ⟨ Fin.append x.1.val x.2.val, by intro i; induction i using Fin.addCases <;> simp [ x.1.property _, x.2.property _ ] ⟩
    invFun y:= (⟨ left0 y.val, fun i=> by have h:= y.property ( Fin.castAdd m i ); rw [ Fin.append_left ] at h; exact h⟩,⟨ right0 y.val, fun i=> by have h:= y.property ( Fin.natAdd n i ); rw [ Fin.append_right ] at h; exact h⟩)
    left_inv x:= Prod.ext (Subtype.ext (funext fun i=> Fin.append_left ..)) (Subtype.ext (funext fun i=> Fin.append_right ..))
    right_inv y:= Subtype.ext (correct y.val) }
def linkQ : ( LivesP p × LivesP q ) ≃ LivesP ( Fin.append p q ) := ( Equiv.prodCongr ( recode p ) ( recode q ) ).trans (( merge p q ).trans (recode _ ).symm )
@[simp] lemma decoder (u:LivesP p)(w:LivesP q): decode ( Fin.append p q ) (linkQ p q (u,w))= Fin.append (decode p u) (decode q w):= congr_arg ( fun v=> v.val ) ( ( recode ( Fin.append p q ) ).apply_symm_apply (merge p q ( ( recode p ) u,(recode q ) w )) )
abbrev Cast (G:Gauge) := (d:ℕ)→ Matrix (Grade G d) (Grade G d) Cn
def cue (B:Cast G)(p q:Q G): Cn:= if h:q.h=p.h then B p.h p.item ( h ▸ q.item ) else 0
variable (B C: Cast G)
lemma report (p:Q G)(v:Grade G p.h): cue B p (own v)= B p.h p.item v:= dif_pos rfl
abbrev play (B:Cast G)(p q:Scan G n): Cn:= ∏ i:Fin n,cue B ( p i ) ( q i )
lemma perf (u:Scan G n)(w:Scan G m): play B (Fin.append p q) (Fin.append u w)= play B p u*play B q w:= by unfold play; rw [ Fin.prod_univ_add ]; simp only [ Fin.append_left, Fin.append_right ]
abbrev concert (B:Cast G)(p:Scan G n)(F: Scan G n→ Cn): Cn:= ∑ i:LivesP p, play B p (decode p i)*F (decode p i)
lemma splits (F:Scan G (n+m)→Cn): concert B (Fin.append p q) F= ∑ i:LivesP p, play B p (decode p i)* concert B q ( fun j=> F ( Fin.append ( decode p i ) j )) := by
    unfold concert; rw [ ← Equiv.sum_comp (linkQ p q), Fintype.sum_prod_type ]; simp only [ decoder, perf, Finset.mul_sum, mul_assoc ]
abbrev Single (p:Q G): Scan G 1:= fun _=>p
def Pause (p:Q G) : Grade G p.h ≃ LivesP (Single p):= (Equiv.funUnique ( Fin 1 ) _ ).symm
lemma solo (p:Q G) (F:Scan G 1→ Cn): concert B ( Single p ) F=∑ i:Grade G (heft p), B ( heft p ) p.item i * F ( Single ( own i ) ):= by
    unfold concert; rw [ ← Equiv.sum_comp (Pause p) ]; simp only [ play, Fin.prod_univ_one, decode, report, Single ]; rfl
lemma concerto (F:Scan G n→ Cn) : concert (B*C) p F = concert B p (fun u=> concert C u F):= by
    unfold concert play; simp_rw [ decode, report, Pi.mul_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul ]; -- rw leftover need product
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by rw [Finset.prod_mul_distrib, mul_assoc]; rfl
lemma cue_one {q:Q G}(i:Grade G q.h): cue 1 q (own i)=if q.item=i then 1 else 0:= by rw [ report ]; rfl
lemma prelude (p:Q G): own p.item=p:=rfl
lemma soloist (F:Scan G n→ Cn): concert 1 p F=F p:= by
    let u:LivesP p:= fun i=> (p i).item; unfold concert; rw [ Finset.sum_eq_single u ];
    · rw [ play ]; simp_rw [ decode ]; rw [Finset.prod_eq_one (fun i _=> (cue_one (u i) ).trans ( if_pos rfl )),one_mul ]; rfl
    · intro i hi hp; obtain ⟨j,hj⟩:= Function.ne_iff.mp hp; exact mul_eq_zero_of_left (Finset.prod_eq_zero (i:=j) (Finset.mem_univ j) ( (cue_one (q:=p j) ( i j )).trans ( if_neg (Ne.symm hj) ) )) _
    simp
end YM.FVA2.O.Score
