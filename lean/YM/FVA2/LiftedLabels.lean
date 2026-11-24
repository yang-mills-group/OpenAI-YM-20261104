import YM.FVA2.MeshJet
import YM.FVA2.MixedRemoval
import YM.FVA2.RankStamp
import YM.Next.FOUNDATIONS.Primary
/-!
# The diction (before and including the top engineering calibration)

 Use `F/H/S` shared choices. Each individual stamp `simple` before top leading inverses
 is also real, covariant in the group, and suitable directly for the existing Tide/Dial
 endpoints. The **actual** `B^a` cards, with W correction, are installed by `native`.
 Signed-axis commutation claims involving these matrices are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 810000
noncomputable section
namespace YM.FVA2
open Filter Topology Set Function MeasureTheory
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Paint
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book
open MS.Cylinder MS.Cylinder.Lab MS.Book.Convolve MS.Plane MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension MS.Theater MS.Local.Physical MS.Menus Plate YM.Source
open Next.Rank Next.Rank.Normal Next.Foundations Labels
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}
structure Warehouse (G:Gauge) where
   F : Frames G
   H : Hol G
   S (d:ℕ): SectionData (F.level d)
   h (d:ℕ) : (S d).Sound H
   acts (d:ℕ): Bid.pop (S d)

namespace Warehouse
variable (Q : Warehouse G) (B: Local.Physical.Deck G)
abbrev scene (d:ℕ) := Q.F.level d
abbrev Atom (d:ℕ):= (Q.scene d).Index
def artifact (d:ℕ) (i:Q.Atom d): Glow G:= (prepared (Q.S d) (Q.h d) (Q.acts d) i).choose
abbrev grade (d:ℕ)(i:Q.Atom d) := ((Q.scene d).grades i).2
abbrev scopeW (d:ℕ):= LatticePT.topMatrix (Q.S d) Q.H (Q.h d) (Q.acts d)
abbrev inftyQ (G:Gauge):=LatticePT.covarianceSymbol G

lemma placed (d i) : Bank (Q.artifact d i) (bare (Q.S d) i) (Q.grade d i) ((Q.scopeW d).basis i) := (prepared (Q.S d) (Q.h d) (Q.acts d) i).choose_spec.1
lemma poised (d i): Source.Brand (Q.artifact d i) (bare (Q.S d) i):= (prepared (Q.S d) (Q.h d) (Q.acts d) i).choose_spec.2
lemma awake (d i): Aura (Q.artifact d i) (Q.grade d i):= (Q.placed d i).aura _ (Q.h d) _
-- bip degree,sumId
def label (d v:ℕ)(i:B.BIndex d v): Labels.Label G d:= ⟨film B i (h:=d), limitH (filmW (h:=d) B i).2, ((cinema _).mp (filmW (h:=d) B i)).2.1⟩
-- remove Q param auto
variable {d r:ℕ}
lemma label_real (i:B.BIndex (d:ℤ) r): Labels.realBar (label B d r i)=label B d r i := Subtype.ext ((cinema _).mp (filmW (h:=d) B i)|>.2.2)
lemma label_grade (i:B.BIndex (d:ℤ) r): label B d r i∈ Labels.Grade (d,r) := (filmW (h:=d) B i).2
variable (u: B.BIndex (d:ℤ) r)
local notation "κ"=> (Q.scene d)
def fits (d r:ℕ)(u:B.BIndex (d:ℤ) r): (Q.scene d).Coeff:= (Q.scene d).coords (Warehouse.label B d r u)
def top (d r:ℕ)(u:B.BIndex (d:ℤ) r) (i:Q.Atom d) :ℝ:= (Q.fits B d r u i).re
def qfits (d r:ℕ)(u:B.BIndex (d:ℤ) r): (Q.scene d).Coeff := (Q.scopeW d).inverse (inftyQ G) (Q.fits B d r u)
def prices (d r:ℕ)(u:B.BIndex (d:ℤ) r)(i:Q.Atom d): ℝ:= (Q.qfits B d r u i).re
lemma fbar : star (Q.fits B d r u)=Q.fits B d r u:= by
    funext i; change star (Q.fits B d r u i) = _; rw [← (Q.scene d).conj_basis, fits, LinearEquiv.symm_apply_apply,label_real]
lemma qlive (d r u): (Q.scopeW d).conversion (inftyQ G) (Q.qfits B d r u)= Q.fits B d r u := ((Q.scopeW d).conversion (inftyQ G)).apply_symm_apply ..
lemma qb : star (Q.qfits B d r u)=Q.qfits B d r u:= by
   apply ((Q.scopeW d).conversion (inftyQ G)).injective; rw [show (Q.scopeW d).conversion _ _=_ from LatticePT.Vertex.bar_map (Q.S d) Q.H (Q.h d) (Q.acts d) (Q.qfits B d r u)]; change star ((Q.scopeW d).conversion (inftyQ G) (Q.qfits B d r u))=_; rw [qlive,fbar]
lemma top_cast i: (↑(Q.top B d r u i):ℂ)=Q.fits B d r u i:= Complex.conj_eq_iff_re.mp (congr_fun (Q.fbar B u) i)
lemma price_cast i: (↑(Q.prices B d r u i):ℂ)=Q.qfits B d r u i:= Complex.conj_eq_iff_re.mp (congr_fun (Q.qb B u) i)
lemma fit_ceil (i:Q.Atom d) (he:((Q.scene d).grades i) ≠(d,r)): Q.fits B d r u i=0:=(Q.scene d).power_coefficient i (Ne.symm he) (label_grade ..)
lemma lower (i:Q.Atom d) (hi:r<Q.grade d i) : Q.qfits B d r u i=0:= by
   unfold qfits; exact (Q.scopeW d).inverse_slots _ (r+1) (fun i H=>Q.fit_ceil B u i (fun h=> ( (congr_arg Prod.snd h).not_gt ( Nat.lt_of_succ_le ( show Q.grade d i≥ r+1 from H ) ) ))) _ (show Q.grade _ i≥ r+1 from hi)
lemma aligns (i:Q.Atom d)(hr:r≤Q.grade d i) : Q.qfits B d r u i=Q.fits B d r u i:= by
   let C:=Q.scopeW d; let x:=Q.fits B d r u; let y := Q.qfits B d r u; let U:= C.conversion (inftyQ G)
   have ht:U y=x := qlive ..; change y i=x i; rw [← ht]; change y i=(∑ j:Q.Atom d, y j • C.joint (milk (inftyQ G) (C.basis j))) i; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; swap; · intro k _ hk; by_cases h:Q.grade d k≤ r; rw [Pi.smul_apply,C.coefficientMatrix (h.trans hr), Pi.single_eq_of_ne (Ne.symm hk), smul_zero]; rw [ show y k=0 from Q.lower B u k (Nat.lt_of_not_ge h), zero_smul]; rfl
   rw [Pi.smul_apply,C.coefficientMatrix le_rfl, Pi.single_eq_same,smul_eq_mul,mul_one]
lemma replica : label B d r u=∑ i:Q.Atom d,Q.fits B d r u i • (Q.scene d).basis i := ((Q.scene d).basis.sum_repr _).symm
lemma scheme : B.raw d r u= Theater.orbit G (label B d r u).val:= (lamp_here B u).symm

def seed (d r:ℕ)(u:B.BIndex (d:ℤ) r) : Glow G:= ∑ i:Q.Atom d, (↑(Q.top B d r u i):ℂ) • Q.artifact d i
def simple : LitBook B where
   stamp:= Q.seed B
   levels _ _ i:=by -- dim
       rename_i d r; apply Aura.sum _; intro j _; by_cases h:r=( (Q.F.level d).grades j ).2; · apply ( Aura.scalar (Q.top B d r i j) ( h.symm ▸ Q.awake d j ) )
       rw [top_cast, fit_ceil,zero_smul]; exact Aura.zero _ _; exact fun h'=>h ( (congr_arg Prod.snd h' ).symm )
   fit d r u:= by
       rw [scheme,replica Q,AddSubmonoidClass.coe_finsetSum,map_sum]; unfold seed; simp_rw [top_cast]; apply Fits.sum; intro j hj; by_cases h : ((Q.scene d).grades j)=(d,r); swap; · rw [fit_ceil Q B u _ h,zero_smul,zero_smul,Submodule.coe_zero,map_zero]; exact Fits.zero _ -- order of rewrites?
       rw [Submodule.coe_smul,map_smul]; apply ( Fits.smul (Q.fits B d r u j) ?_ ); convert Plate.realistic (Q.S d) (Q.h d) (Q.acts d) j (Q.placed d j) using 1; exact (congr_arg Prod.snd h).symm; rw [h]

def formula (d r:ℕ)(i:B.BIndex d r) : Source.Weights G:= ∑ j:Q.Atom d,Q.top B d r i j • bare (Q.S d) j
def diction : Source.NativeDictionary B where
   book:= Q.simple B
   formula:= Q.formula B
   stamps d r i:= by
      suffices hv:∀ s:Finset (Q.Atom d), Source.Brand (∑ j∈s, (↑(Q.top B d r i j):ℂ) • Q.artifact d j) (∑ j∈s, Q.top B d r i j • bare (Q.S d) j) from hv Finset.univ
      intro s; induction s using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact Source.Bzero| insert j s hj ih=> rw [Finset.sum_insert hj,Finset.sum_insert hj]; exact Source.Badd (Source.Bcash (Q.poised d j) _) ih
-- mix into all off-shell stencils at this horizon
open LatticePT
abbrev inkB (d:ℕ)(i:Q.Atom d):= Book.levels (Q.grade d i) (Q.artifact d i)
def code (d:ℕ)(z:Q.Atom d→ℝ) : T (Dot G Cover):= ∑ i:Q.Atom d,(↑(z i):ℂ) • Q.inkB d i
def native : BookM B where
   inkM d r i := Q.code d (Q.prices B d r i)
   fitM d r i:= by
      have ht := (Q.simple B).fit d r i; change Fits (Q.seed B d r i) _ _ _ _ at ht; unfold Fits at *; convert ht using 1; unfold seed code; simp only [Finset.sum_apply,map_sum,map_smul,Pi.smul_apply,top_cast,price_cast]; exact Finset.sum_congr rfl (fun j _=> by
        by_cases h:r=( (Q.F.level d).grades j ).2
        · rw [Q.aligns B _ j h.le]; congr 1; rw [ inkB, Book.levels,Tone.grade ]; rw [show ( (0:ℕ):ℤ)+Q.grade d j=r by exact_mod_cast ( (Nat.zero_add (Q.grade d j) ).trans h.symm )]; exact Glyph.mask_sq ..
        rcases lt_or_gt_of_ne h with h|h; · rw [Q.lower B _ _ h,Q.fit_ceil B _ j (fun ht=> h.ne (congr_arg Prod.snd ht|>.symm)),zero_smul,zero_smul]
        rw [inkB,Book.levels,Tone.grade, Q.fit_ceil B _ j (fun he=> h.ne' ((congr_arg Prod.snd he).symm)), zero_smul, Book.rank_off (Book.rankMod (run (Q.artifact d j)) (↑(0:ℕ) + ↑(Q.grade d j))) (by change Q.grade d j<r at h; omega),smul_zero] )
   tuneM d r u k:= by unfold code; rw [Finset.sum_apply]; apply Tune.sum _; intro i _; exact (TuneModel (Q.awake d i).phase _).cash _ (by simp)
   lightM d r u k:= by unfold code; rw [Finset.sum_apply]; exact Colorless.csum _ fun i _=> (ColorMod (Q.awake d i).lit _).smul _
   boundM d r u k:= by
      unfold code; rw [Finset.sum_apply,sum_stack]; refine Limit.sum _ fun i _=>?_ ; rcases le_or_gt (Q.grade d i) r with h|h; · exact Limit.smul _ (Limit.up (Limit.mod (Q.artifact d i).val ((k:ℤ)+(Q.grade d i:ℤ))) (by omega))
      rw [Q.price_cast, Q.lower _ _ _ h,zero_smul]; exact fun _ _=>rfl
   weightM d r u h:= by
      let D := MS.Book.actB (Spectrum G) + MS.Book.blocks (Spectrum G) (core G);
      change D _=0; unfold code; rw [map_sum]; exact Finset.sum_eq_zero fun i _=>by rw [map_smul, show D _=0 from (Q.awake d i).closed h,smul_zero]
end Warehouse
namespace Plate
lemma storage (G:Gauge): Nonempty (Warehouse G):= by
   exact ⟨⟨ Labels.frames G, Next.Foundations.hol G, Next.Foundations.localSection G, Next.Foundations.sound G,Next.Foundations.valuation _ ⟩⟩ -- adjust
end Plate
end YM.FVA2
