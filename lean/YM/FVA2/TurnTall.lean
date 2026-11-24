import YM.FVA2.AverageMarks
/-!
# Auxiliary dimension rotation group on DR kernels

Coeff families before 4D projection, compatibility with arbitrary evanescent ker Sturdy.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.ArchTurn
open MS MS.Local.Physical MS.Menus MS.SpinCode MS.Rake MS.Plane MS.City
open ColorCode Plate Filter Topology Set Function MeasureTheory PertExtension
open Wilson Lattice MS.Native MS.Native.Wilsonian MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Arts.Spin MS.Halo
open scoped Topology Classical ContDiff
variable {G:Gauge} (s:Signed) {m n:ℕ} (h:m≤n)
-- semigroup law on arch; no closed PCI.
section spin
variable {A:Type}[Fintype A] [DecidableEq A] (X Y : Arts.Spin A)
def after : Arts.Spin A where
   turn:= Y.turn.trans X.turn
   rad i j:= by change Momentum.pairing ( X.turn (Y.turn i)) (X.turn (Y.turn j))=_; rw [X.rad,Y.rad]
lemma price (i j:A) : (after X Y).profile i j=∑ k:A,Y.profile i k*X.profile k j:= (X.orth (Y.turn (spray i)) j).symm
lemma priceC (i j:A) : ((after X Y).profile i j:ℂ)=∑ k:A,(Y.profile i k:ℂ)*(X.profile k j:ℂ):= by rw [price,Complex.ofReal_sum]; push_cast; rfl
lemma fuses {C:Type}[Fintype C][DecidableEq C] (l: Legs (Mode (Leg A C) (Momentum A))) (F:Row (Leg A C) (Momentum A) ℂ) :
   (leggo C Y).beam ((leggo C X).beam F) l=(leggo C (after X Y)).beam F l:= by
   induction l generalizing F with
   | nil=> simp
   | cons a l ih=>
      let N:= (leggo C X); obtain ⟨⟨⟨_|a,b⟩,c⟩,p⟩:=a;
      · rw [fromG,fromG,show D (((none,b),c),Y.turn p) (Pilot.beam N F) =N.beam ( D (((none,b),c), X.turn (Y.turn p)) F) from funext fun i=>fromG .. ]; exact ih _
      rw [ fromV, fromV ]; have he i : D (((some i,b),c),Y.turn p) (N.beam F)=∑ j:A,(X.profile i j:ℂ) • N.beam (D (((some j,b),c), X.turn (Y.turn p)) F):= funext (fun l=> by rw [at_D,Finset.sum_apply]; exact fromV ..)
      unfold N at he; simp_rw [he,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,ih,smul_eq_mul,Finset.mul_sum,← mul_assoc, priceC X Y, Finset.sum_mul]; rw [Finset.sum_comm ]; rfl
lemma back_after {C:Type}[Fintype C][DecidableEq C] (l:Legs (Mode (Leg A C) (Momentum A))) (F): (leggo C (after X X.back)).beam F l=F l:= by
   let Z:=after X X.back; have he(p:Momentum A): Z.turn p=p:=front X
   induction l generalizing F with
   | nil=> simp
   | cons a l ih=> obtain ⟨⟨⟨_|a,b⟩,c⟩,p⟩:=a; · rw [fromG,ih,he]; rfl
                   change (leggo C (after X X.back)).beam F ((vleg b a c,p)::l)=_; rw [cols (X:=after X X.back) (show Z.turn (spray a)=(1:ℝ) • spray a from (he _).trans (one_smul ..).symm) _ b c _ _, Complex.ofReal_one,one_mul, ih, he ]; rfl -- order of tactic columns maybe
end spin

abbrev crane := Spin.arch (m:=0) (Nat.zero_le n) -- incomplete application X implicit? actual notation macro n
-- prefix, typing at n parameter
abbrev arcS (n:ℕ)(s: Signed): Spin (Arts.L n) := crane (n:=n) (Outlook.hand s)
def whorl (n:ℕ)(s:Signed) := (flagS (arcS n s) G).beam

def canto : Mob G→ₗ[ℂ] Mob G where
    toFun F n:= whorl n s (F n)
    map_add' i j:= funext fun n=> map_add _ (i n) (j n)
    map_smul' i j:= funext fun n=>map_smul _ i (j n)

private lemma spin_ext {A:Type}[Fintype A]{X Y:Spin A}(h:∀ p:Momentum A,X.turn p= Y.turn p): X=Y:= by rcases X with ⟨K,F⟩; rcases Y with ⟨L,H⟩; change ∀ p,K p=L p at h; obtain rfl:=ContinuousLinearEquiv.ext (funext h); rfl
lemma frameset (X Y:Spin (L m)): arch h (after X Y)= after (arch h X) (arch h Y):= by
    apply spin_ext; intro p; change _=(arch h X).turn ((arch h Y).turn p); rw [← Arts.city h p, map_add (arch h (after X Y)).turn,map_add,map_add]; simp only [arch_identity,arch_on]; rfl
lemma reflexA (X:Spin (L m)): arch (le_refl m) X=X:= by
    apply spin_ext; intro p; have he (p:SectorP m): Left (le_refl m) p=p:= funext fun i=> lasts _ p i; simpa only [he] using arch_on (le_refl _) X p
lemma backx (X:Spin (L m)): arch h X.back=(arch h X).back:= by
    apply spin_ext; intro p; apply (arch h X).turn.injective; rw [← Arts.city h p,map_add (arch h X.back).turn,map_add,arch_on,arch_identity,arch_identity,arch_on,front,front]; -- syntax
lemma forever (p u:Signed) (n:ℕ) : arcS n (p*u)= after (arcS n p) (arcS n u) := by unfold arcS crane; rw [← frameset]; congr; apply spin_ext; intro i; exact Signed.act_mul p u _
private lemma another (X:Spin (L n)) (hL:X.within false): (after (arcS n s) (after X (arcS n s).back)).within false := by
   intro hx i; rw [show (after _ _).turn ( Left (Nat.zero_le n) i)=(arcS n s).turn ( X.turn ((arcS n s).back.turn (Left (Nat.zero_le n) i))) from rfl, arcS, crane,← backx,arch_on,hL rfl _, arch_on,front ]
lemma inter (X:Spin (L n)) (V:Rack G n) : (flagS X G).beam (whorl n s V)=whorl n s ((flagS (after (arcS n s) (after X (arcS n s).back)) G).beam V):= by
   funext l; unfold whorl flagS; rw [ fuses _,fuses _ ]; refine congr_arg (fun Z:Spin (L n)=> (leggo G.ColorIndex Z).beam V l) ?_;  apply spin_ext; intro p; let C:= (arcS n s); change C.turn ( X.turn p )= C.turn (X.turn (C.back.turn ( C.turn p )) ); rw [rear]
-- arch additive all horizons. show via Left, additional basis left image then right beyond. command sub. simplif via expression turn total leftG correction to p using Cl.
lemma add_r (X:Spin (L m))(p:SectorP n): (arch h X).turn p= p+ Left h ( X.turn (Cl h p)-Cl h p):= by
   rw [show (arch h X).turn=(Spin.taller h X) from rfl,Spin.total,map_sub]; obtain he:= Arts.city h p; rw [show Right h (Cr h p) = p - Left h ( Cl h p ) from eq_sub_of_add_eq (by rw [add_comm,he])]; abel
lemma forward (X:Spin (L 0)): arch (Nat.zero_le n) X= arch h (arch (Nat.zero_le m) X):= by
    apply spin_ext; intro p; simp_rw [ add_r, add_sub_cancel_left ]; unfold Left; rw [sons,rides_link]; rfl
lemma sturdy_s (F:Mob G)(he:Sturdy false F): Sturdy false (canto s F) := by
    refine ⟨fun i X H=> Eq.trans (inter s X (F i)) (congr_arg _ (he.turn i _ (another s X H))),fun i l=>?_⟩;
    unfold canto; dsimp; unfold whorl arcS crane; rw [forward i, Spin.telescopeS i, funext (he.grows i)]
lemma ceiling0 (V:Rack G 0) : whorl 0 s V = backlit s V := by unfold whorl arcS crane; rw [reflexA]; rfl
lemma v_owner {K:Spin (Arts.L n)} : K.back.back=K:= by apply spin_ext; intro p; rfl
lemma verses (s:Signed) : arcS n s⁻¹=(arcS n s).back := by
    apply spin_ext; intro p; apply (arcS n s).turn.injective; let x:= arcS n s; rw [show x.turn ((arcS n s⁻¹).turn p)= (arcS n (s*s⁻¹)).turn p from by rw [forever]; rfl,mul_inv_cancel,front ]; unfold arcS crane; rw [ add_r (Nat.zero_le n) ]; -- simp
    rw [ show ∀ i:Momentum Axis,(Outlook.hand (1:Signed)).turn i= i from fun p=> Signed.act_one p, sub_self,map_zero,add_zero ]
end YM.FVA2.ArchTurn
