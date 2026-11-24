import YM.FVA2.Position.Ace
/-!
# Unit on the actual insertion frame. Top and MS read on weight zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Ace
open Function Set Filter Finset MeasureTheory Lattice Wilson
open MS MS.Momentum MS.Arts MS.Koszul MS.Plane MS.Theater MS.Garment MS.Wind
open MS.Pearl MS.Rock MS.Alps MS.Halo MS.Mach MS.Motif MS.Native.Paint
open MS.Hem MS.Hem.Mell MS.Dock MS.Train _root_.YM.MS.Shine MS.High MS.High.Knobs
open MS.Outlook MS.Color MS.Native MS.Native.Wilsonian MS.Landau MS.Landau.Detect
open MS.Book MS.Book.Program MS.Book.Convolve MS.Heat MS.Local.Physical MS.Land
open Garment.Wave Garment.Wick MS.Emit MS.Cylinder MS.Cylinder.Lab MS.Menus MS.City
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n:ℕ}{G:Gauge} (p:Team)
local notation "W"=> Glyph
local notation "Z" => Press.portDeck G
--local notation "F"=> Plaid (Press.portDeck G) 0
local notation "A"=> (Finsupp.single 0)
lemma cost0 (f:Plaid Z 0): ∃ t:ℝ, film Z f.2 (h:=0)=MvPolynomial.C (t:ℂ):= by
    let t:= Press.beginning f.2 (w:=0); obtain he:f.1.val=0:=(by have he:= f.1.isLt; omega); have hp:t∈Labels.Grade (0,0) := (show t ∈ Labels.Grade (0, f.1.val) from Press.primary f.2 (w:=0)) |> (fun h=> by rwa [he] at h); obtain ⟨k,hk⟩:= Labels.scalar_grade 0 hp
    obtain hz:= Press.reality f.2 (w:=0); change Labels.realBar t=t at hz; rw [hk,Labels.realBar.map_smulₛₗ,Labels.unit_real] at hz
    replace hz: star k=k:= smul_left_injective ℂ Labels.unit_not_zero hz; obtain ⟨v,rfl⟩:= Complex.conj_eq_iff_real.mp hz; refine ⟨v,?_⟩; change t.val=_; rw [hk]; change (v:ℂ) • (1:Labels.Pol G)=_; rw [ Algebra.smul_def,mul_one ]; rfl -- prior rewrite tag `F` lens
-- native program
variable (Y:XSpace.Initialize G)
local notation "ℳ"=> Press.wickInput Y
variable {t: ℝ} {X:Dot G Cover} {i:ℕ}
lemma floor_one (n:ℕ)(c:ℂ) : Book.levels 0 (Cylinder.piece c:Dot G Cover) n= UnitF ( Cylinder.piece c:Dot G Cover ) n:= by
    rcases n with _|n; · exact Subtype.ext (show Book.mask (0+0) _= _ from rank_hat (0:ℤ)|>.mp (Rails.coin c))
    apply Subtype.ext; ext l; cases l with| nil=> change ( Book.mask ((n+1:ℕ)+0:ℤ) (coin c: Raw (LightMode G Cover) ℂ) [])=0; rw [strange [] (by dsimp; omega)] | cons i l=> simp [Book.levels,mask_s, Cylinder.piece, Book.mask,coin, UnitF]
lemma center (c:Cn)(F:Dot G Cover): substitute c (UnitF F)=UnitF F:= by
 funext j; rw [rules]; rw [Finset.sum_eq_single 0]
 · simp only [ UnitF, if_true,Program.cut,pow_zero,PowerSeries.coeff_one]; split_ifs <;> simp_all
 · intro a h he; rw [ UnitF, if_neg he,smul_zero];
 simp
lemma pointθ (z:ℂ)(F: LightMode G Cover →Cn): train F n (Cylinder.piece z)=UnitF (Cylinder.piece z) n:=by
    apply Subtype.ext; ext l; rw [train_v, Program.offer]; cases n with| zero=> simp [ UnitF, Cylinder.piece]; cases l <;> simp [coin] | succ n=> cases l <;> simp [ UnitF, Cylinder.piece, coin, PowerSeries.coeff_one]
lemma raised (c:ℂ)(x:ℝ): wobble G p x (UnitF (Cylinder.piece c))=UnitF (Cylinder.piece c):= by
    funext n; unfold wobble; rw [LinearMap.comp_apply, center,Program.rolls, Finset.sum_eq_single (n,0)]; · exact pointθ ..
    · intro j h he; obtain hx:= Finset.mem_antidiagonal.mp h; rw [UnitF, if_neg (by intro h; exact he (Prod.ext (by omega) h) ), map_zero]; -- patch
    simp
lemma gallery0 {g:W Z 0} (t:ℝ) (ht:film Z g.2.2 (h:=g.size) (r:=g.grade)=MvPolynomial.C (t:ℂ)): Glyph.gallery ℳ g=UnitF (Cylinder.piece (t:ℂ)):= by
    unfold Glyph.gallery Glyph.Bundle; rw [Fintype.sum_sum_type,Fintype.sum_unique]; have hv:g.grade=0:= le_antisymm (Glyph.memory g) (Nat.zero_le _)
    rw [Finset.sum_eq_zero (s:= Finset.univ (α:=Fin ( g.size+1 )×Fin g.grade)) (fun i _=>False.elim (by have hk:= i.2.isLt; omega)),add_zero, Press.stampF ]; change levels g.grade ( Press.dot _ (film _ _ (h:=g.size)))=_; rw [ht,hv, ← show Press.sat (Y.surveys g.size) ( MvPolynomial.C (t:ℂ) )= _ from Press.sat_real _ _ (by simp [Labels.conjPol]), Press.sat_constant, show ( ( t:ℂ ) • (Cylinder.piece 1:Dot G Cover))=Cylinder.piece ( t:ℂ ) from ?_ ]; · exact funext fun n=> floor_one n (t:ℂ)
    apply Subtype.ext; ext l; cases l <;> simp [ Cylinder.piece,coin ]
set_option maxHeartbeats 200000 in
lemma glo (i:Plaid Z 0)(t:ℝ)(h:film Z i.2 (h:=0)= MvPolynomial.C (t:ℂ)) (x:ℝ): (Land.read i).preambleF ℳ p x=UnitF (Cylinder.piece (t:ℂ)):= by unfold Glyph.preambleF; let g:= Land.read i; have hk:film Z g.2.2 (r:=g.grade) (h:=g.size)=MvPolynomial.C (t:ℂ):= h; rw [ gallery0 Y (g:=Land.read i) t hk]; exact raised p _ _
end YM.FVA2.Position.Ace
