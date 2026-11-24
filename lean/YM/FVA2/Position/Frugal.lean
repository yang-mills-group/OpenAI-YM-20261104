import YM.FVA2.Position.Favors
/-!
# H-equivariant prescription (actual MS)

Here upgrade to a fee assignment satisfying `Horder` by averaging over the finite H.
This includes *all marked* entries. Ingredients:

* `co_line`: retain the `Fixed` estimates on mark kernels. Uses `archiveH` (the actual MS
  pole prescription, not postulating orientation invariance of every possible continuation)
* `fitF`, `mainL`: retain the `FitOrder` prescription incl. rank condition on the leading entries
* `move`, `Held`, `market`: conclude this implements `Horder`
* `upgrades`: copy the `team`, retain all `TaylorOKF` requirements. Additional requirements
  on mark frames (unit, strict rank etc.) as needed in `Main.lean` are treated elsewhere.

Not asserting anything about the symmetry of the actual theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Favors
open Function Set Filter Finset MeasureTheory Lattice
open MS MS.Plane MS.Tone MS.Koszul MS.Heat MS.Book MS.Landau MS.Landau.Detect MS.Momentum MS.Plane.Wire
open MS.Native MS.Native.Wilsonian MS.City MS.Tone.Frame MS.Arts MS.Outlook MS.Color MS.Native.Paint
open MS.Book.Program MS.Book.Convolve MS.Cylinder.Lab MS.Cylinder
open Brass MS.Wind MS.Wind.Leading MS.High MS.High.Knobs MS.Logarithm MS.Menus MS.Land Axes Wheel Crosswind
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n d:ℕ}{J:Type}{G:Gauge}{u:ℤ}(s t:Signed)
local notation "B"=> Press.portDeck G
local notation "𝓜"=> Glyph B d
-- use at every clock.
variable (Y:XSpace.Initialize G) {p:Team}
local notation "ℳ"=> Press.wickInput Y
open Native.Orient
variable (S:MS_Data G ( OpenAxis.Plot ( Press.portDeck G )))
abbrev DMark (G:Gauge) (d:ℕ):= Plaid ( Press.portDeck G ) d
local notation "Ω"=> DMark G d
variable (F:DMark G d→ Acts (Press.portDeck G) d) (M': Prescription (Press.portDeck G))
lemma sizeW (c:Ω): (Land.read c).grade=c.1.val:= rfl
abbrev pin (i:Ω)(c:Case G d i.1.val) : DMark G d:= ⟨i.1,c⟩
local notation "vS"=> markS s G d
-- `pose` on output. Push label grade exactly; input already rotated by inverse.
def divert (s:Signed)(F:DMark G d→Acts B d)(i:Ω) : Acts B d:= stepF Finset.univ (markS s⁻¹ G d i.1.val i.2) (fun j=> lifted s (F (pin i j)))

lemma co_line (h:∀ i:Ω, Fixed (col (horizonF ℳ p (F i))) (Archive d ( S.marks d i)) false d 0)(i:Ω): Fixed ( col (horizonF ℳ p (divert s F i))) (Archive d ( S.marks d i)) false d 0:= by
    let U:= fun (j:Ω)=> Archive d ( S.marks d j); let X(j:Case G d i.1.val):= S.marks d (pin i j); let f:= markS s⁻¹ G d i.1.val i.2; let A(c:Case G d i.1.val) (n:ℕ) := α s⁻¹ ∘ U (pin i c) n; have he: Archive d ( S.marks d i)=∑ j,f j • A j:= by
        -- archiveH at s^-1 identifies ∑ j m(s^-1) ... S_j =alpha s U_i. then cancel rotate.inv. orientation.
        funext n x; obtain ⟨y,z⟩:= x; let L:= Archive d ( S.marks d i) n (y,z); have hk: α s L= ∑ j:Case G d i.1.val, f j • U (pin i j) n (y,z):= inv_inv s ▸ Park.archiveH (s⁻¹) S i n y z -- casts peril
        have hL: α s⁻¹ (α s L)=L:= by rw [α, α, handInv]; exact Weft.beam_inv' (m:=0) _ _
        change L=_; rw [← hL,hk]; simp_rw [Finset.sum_apply,map_sum]; exact Finset.sum_congr rfl (fun i _=> map_smul ( ( α (G:=G) s⁻¹ ).restrictScalars ℝ) _ _) -- metavars
    rw [he,divert,total_H, col_sum]; refine fixed_sum _ (fun i hi=>?_ ) _; rw [stairs]; exact frameQ s⁻¹ ( h (pin _ i) )
-- FitOrder. Keep rank through these transformations; prove strictly rank lowering using equality Kronecker choose via lenses.
lemma lower_r {S: Finset J}(f:J→ℝ){X:J→Acts B d}(h:∀ i∈S,∀ x:ℝ, Limit ((X i n).proof.input x).val u) (x:ℝ): Limit ((stepF S f X n).proof.input x).val u:= by unfold stepF bigH; simp_rw [Finset.sum_apply,sum_stack]; exact Limit.sum _ (fun i hi=> ( h i hi x ).smul ( ( f i:ℝ ):ℂ ))
lemma prism (x: Glyph B d)(y:Ω): (x.1= (read y).1 ∧ x.grade=y.1.val) ∨ ∀ (i:Case G x.size x.grade)(j:Case G d y.1.val), Axes.take x i ≠ read (pin y j) := by
    by_contra hx; push Not at hx; obtain ⟨h,i,j,H⟩:= hx; exact h ( show x.1= _ from (show (Axes.take x i).1=(Land.read (pin y j)).1 from congr_arg Sigma.fst H) ) ( show (Axes.take x i).grade=( Land.read (pin y j) ).grade from congr_arg (fun i:Glyph B d=> i.grade) H )
lemma fitF (i:Ω)(h:∀ i:Ω, FitOrder (Land.read i) ( F i 0 )): FitOrder (Land.read i) ( divert s F i 0 ):= by
    refine ⟨ fun x=> lower_r _ (fun j _ x=>limits_p s (( h (pin i j)).Low x)) x, ?_⟩; intro a hA; by_cases hx : (a.1 = (read i).1 ∧ a.grade=i.1.val); swap; · obtain hx':= (prism a i).resolve_left hx; rw [if_neg (fun he=> hx ⟨congr_arg Sigma.fst he, congr_arg ( fun i:Glyph B d=> i.grade ) he⟩ ) ]; unfold divert stepF lifted erect; simp_rw [ Finset.sum_apply, Pi.smul_apply ]; apply Finset.sum_eq_zero; intro j _; rw [ Finset.sum_eq_zero ( fun k _=>?_) , smul_zero ]; rw [( h (pin i j) ).Single (Axes.take a k) ( show _ from (hA: (Land.read (pin i j)).grade ≤ (Axes.take a k).grade) ), if_neg ( hx' _ _ ), smul_zero ]
    obtain ⟨k,hk⟩:∃ k:Case G d i.1.val, a= read (pin i k):= by
       rcases a with ⟨b,y,w⟩; rcases i with ⟨i,l⟩; obtain ⟨h1,h2⟩:=hx; change b=(⟨d,Nat.lt_succ_self d⟩ : Fin (d+1)) at h1; subst b; replace h2 : y= i:= Fin.ext h2; subst i; exact ⟨w,rfl⟩
    subst a; have hc (i:Fin (d+1)) (a b:Case G d i.val): read (⟨i,a⟩: Plaid B d)=read (⟨i,b⟩:Plaid B d) ↔ a=b:= by unfold Land.read; simp
    let l := read (pin i k); have hv(j:Case G d i.1.val): erect (s:=s) ( F (pin i j) 0 ).register l= markS s G d i.1.val j k • (1:Poly):=by
      unfold erect; change ∑ a:Case G d i.1.val,markS s G d _ a k • ( F (pin i j) 0).register ( Land.read (pin i a) )=_; simp only [(fun i0=> ( h (pin i j)).Single (Land.read (pin i i0)) ( Nat.le_refl i.1.val )), pin, hc ]; rw [Finset.sum_eq_single j]; · rw [if_pos rfl];
      · intro b _ he; rw [if_neg he, smul_zero]
      simp
    rcases i with ⟨u,i⟩; change ( ∑ x:Case G d u.val, markS s⁻¹ G d u.val i x • fun g=> erect s (F ( ⟨u,x⟩ ) 0 ).register g ) l=_; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply]; simp_rw [ show ∀ j:Case G d u.val, erect s ( F ⟨u,j⟩ 0 ).register l= _ from fun j=> hv j, smul_smul, ← Finset.sum_smul, pin,hc ]; -- issue hc
    rw [← pack s s⁻¹ i k, mul_inv_cancel, start]; by_cases he:i=k <;> simp [he,Ne.symm]
abbrev θ : ℝ:= (Fintype.card Signed:ℝ)⁻¹
lemma paid {E:Type}[AddCommGroup E][Module ℝ E](x:E): (∑ _:Signed, θ • x)=x:= by
    have he:(Fintype.card Signed:ℝ)≠0:= by positivity
    rw [Finset.sum_const, Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ, show θ=( ( Fintype.card Signed:ℝ ) )⁻¹ from rfl, smul_inv_smul₀ he]
-- actual H solution.
def aspired (F:DMark G d→Acts B d)(i:DMark G d) : Acts B d:= stepF Finset.univ (fun _:Signed=>θ) (fun s=> divert s F i)
lemma mainL (h:∀ i:Ω, FitOrder (Land.read i) ( F i 0 ))(i:Ω): FitOrder ( Land.read i ) (aspired F i 0) := by
    refine ⟨ fun x=> lower_r _ (fun i' _ x=> (fitF i' F i h).Low x) x,fun j hj=>?_ ⟩; unfold aspired stepF; simp_rw [ Finset.sum_apply,Pi.smul_apply, fun j'=> ( fitF j' F i h ).Single j hj, paid]
lemma Boundary (h:∀ i:Ω, Fixed (col (horizonF ℳ p (F i))) (Archive d ( S.marks d i)) false d 0)(i:Ω): Fixed ( col (horizonF ℳ p (aspired F i))) (Archive d ( S.marks d i)) false d 0:= by
    unfold aspired; rw [ total_H, col_sum, ← paid (Archive d (S.marks d i)) ]; exact fixed_sum Finset.univ (fun s _=> co_line s Y S F h i) (fun _=> θ)
-- ensure actual costs strictly fixed at all x, no represent basis at any width. Equality of `register` polynomials before evaluating.
abbrev move {E:Type}[AddCommMonoid E][Module ℝ E] (s: Signed)(K:DMark G d→ E) (y:Ω) := ∑ j: Case G d y.1.val, markS s G d y.1.val y.2 j • K (pin y j)
lemma banner (f:Ω)(i:ℕ): (divert s F f i).register= move s⁻¹ (fun j=> erect s (F j i).register) f:= rfl
lemma move_e {E:Type}[AddCommMonoid E][Module ℝ E](K:DMark G d→ E)(y:Ω): move 1 K y=K y:= by unfold move; simp_rw [ start,ite_smul, one_smul,zero_smul ]; simp
lemma move_l {E:Type}[AddCommMonoid E][Module ℝ E](K:DMark G d→ E)(y:Ω): move s (move t K) y=move (t*s) K y:= by
 rcases y with ⟨y,x⟩; unfold move; simp_rw [Finset.smul_sum, smul_smul,pin]; change (∑ j:Case G d y.val,∑ b:Case G d y.val, (markS s G d _ x j*markS t G d _ j b) • K ( ⟨ y,b⟩ ))= _; nth_rw 1 [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro i hi; rw [pack,Finset.sum_smul]
lemma move_sum {E:Type}[AddCommMonoid E][Module ℝ E](K:J→ DMark G d→ E)(y:Ω)(S:Finset J)(c:J→ℝ): move s (fun x=>∑ j∈S,c j • K j x) y=∑ j∈S,c j • move s ( K j ) y:= by
 unfold move; simp_rw [ Finset.smul_sum ]; nth_rw 1 [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl (fun j _=> smul_comm ..)
def Held (F:DMark G d→Acts B d) : Prop:= ∀ (y:Ω)(s:Signed)(n:ℕ), move s (fun i=> ( F i n ).register) y= erect s ( F y n ).register
lemma erected (F:Ω→Acts B d)(g:Ω)(n:ℕ) : move t (fun y=> erect s (F y n).register) g= erect s (move t (fun y=> (F y n).register) g):= (erect_sum (d:=d) (G:=G) s _ _ _).symm
lemma fundT (y:Ω)(n:ℕ): move s (fun i=> ( divert t F i n ).register) y = erect s ( divert (s⁻¹*t) F y n ).register:= by
    simp only [banner, move_l, mul_inv_rev,inv_inv]; rw [erected t]; rw [erected (s⁻¹*t)]; funext i; rw [← erect_t, mul_inv_cancel_left];
set_option maxRecDepth 4096 in
lemma market (y:DMark G d)(n:ℕ): move s (fun i=> (aspired F i n).register) y = erect s (aspired F y n).register := by
 unfold aspired stepF; dsimp only; change move s (fun j=>∑ t:Signed, θ • ( divert t F j n ).register) y= erect s ( ∑ t:Signed, θ • ( divert t F y n ).register)
 let Q : Signed→DMark G d→ Price B d := fun t j=> (divert t F j n).register
 have hx := move_sum (G:=G) (d:=d) (E:= Price B d) s Q y Finset.univ (fun _=>θ)
 have he := erect_sum (G:=G) (d:=d) s Finset.univ (fun _:Signed=>θ) (fun t=> Q t y)
 change move s (fun j=>∑ t:Signed, θ • Q t j ) y= erect s ( ∑ t:Signed, θ • Q t y ); rw [hx,he]; apply Fintype.sum_equiv (Equiv.mulLeft s⁻¹); intro t; refine congr_arg (θ • ·) ?_; exact fundT s t F y n
lemma locked : Held (d:=d) (aspired F):= fun y s n=> market s F y n
-- H-equivariance at this `Prescription`. For every horizon
-- the mark-fee register orients by `Signed`.
structure Horder (A:Prescription B): Prop where
    property (d:ℕ) : Held ( A.fees d )

def Norm₀ (A:Prescription B) : Prescription B :=
    ⟨ A.team, fun d=> aspired (A.fees d), fun d=> mainL _ (A.init d)⟩

set_option maxRecDepth 4096 in
theorem upgrades (A : Prescription B) (h : TaylorOKF S (Press.wickInput Y) A) :
      TaylorOKF S (Press.wickInput Y) (Norm₀ A) ∧ Horder (G:=G) ( Norm₀ (G:=G) A ) := by
 constructor
 · constructor
   · change Fixed ( col ( skyline G A.team )) _ _ _ _; exact h.bulk
   intro k y; change Fixed (col (horizonF (Press.wickInput Y) A.team ( aspired (A.fees k) y ))) _ _ _ _; exact Boundary Y S (A.fees k) (h.mark k) y
 constructor; intro k; change Held (aspired (A.fees k)); exact locked (A.fees k)
end YM.FVA2.Position.Favors
