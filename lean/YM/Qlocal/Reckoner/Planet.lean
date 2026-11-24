import YM.Qlocal.Reckoner.Stamp
import YM.Qlocal.Versal.Tack
import YM.Qlocal.Parabola.Bunker
/-!
# At the actual step borrow via the full temporary marker palette

Roster_real finite ∋ both analytic log terms with Pose eligibility and any
old decomposed remainder, labels IMAG and status assignments. Inject its indices into
`Whole`, the temporary marker algebra. Can also retain dormant names there. Issue one room book Scriptor (pure tagged monomials for exponent) and coherent reserve on the resulting forced ledger. This allows surgery of M5 localized interactions, travelling to P* already. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories Emissions
variable {V I Ω J J' J₀:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{p:BudgetPoint}{o:V→ Site n}{s:V→ Support n}{q:Ray R} {A A' B u v a r t w δ:ℝ}
open Merge Switch UniformPays
namespace Planet
variable [Fintype V]
-- no changing retained vacuum. buys before questions. Lean under Classical to avoid every D.sh
noncomputable abbrev Whole (V:Type)[DecidableEq V][Fintype V]: Census V:= ⟨univ,mem_univ _,fun _ => mem_univ _,fun {_} _ _ _=> mem_univ _⟩
abbrev pack (T:Finset V): (Whole V).Mode:=⟨T,mem_univ _⟩
set_option quotPrecheck false
local notation "Ψ"=> Whole V
noncomputable abbrev glyph (u: V):Poly (Whole V):= Poly.send (pack {u}) 1
@[simp] lemma glyph_fire (u:V):glyph u=Poly.send ((Whole V).fire u) 1 :=rfl
lemma invoice (p:Finset V): ∏ u∈p,glyph u=Poly.send (pack p) 1:= by
 have h:Fits (Ψ).fire p:=⟨fun i _ j _ hij=> by change Disjoint ({i}:Finset V) {j}; simp [hij],mem_univ _⟩
 have hh:unionTag ((Whole V).fire) p h=pack p:= by ext1; simp [unionTag, pack, Census.fire] -- syntax ext1 binder?
 rw [show (∏ u∈p,glyph u)=Poly.send _ _ from tagged_prod _ p h (fun _=>1)]; rw [hh,prod_const_one]
variable (f:I↪V) [Fintype I] -- expense ontology before layout α. Can drop Dec Eq α.Work
local notation "ℓ"=> fun i:I=>glyph (f i)
abbrev book (p:Finset I):= pack (p.map f)
local notation "u'"=> book f
abbrev mantra (q:Spectrum Ω I G n J)(f:I↪V): Scribe Ω J G n (Whole V):=
     ⟨fun i=> book f (q.tag i), q.region, q.total, fun x i U=> Complex.ofReal (q.raw x i U)⟩
lemma zProp (U : Finset I): zProd (Z:=ℓ) U=Poly.send (book f U) 1:=by rw [← invoice (U.map f),Finset.prod_map]
lemma glyphs_paid (c:Ray (Whole V)) (h: ∀ i,c (book f i) ≤ B): Brand (ℓ) c B:= fun i=> by rw [zProp f i, singletonPrice,norm_one,mul_one]; exact h i
open RGComparison01 RGComparison01.Pledge PhysicalNext Repeat Mallow Blush
variable {Z:Ω→J→ Config G n→ Ways I}{K:WayK Ω I G n} (T: Spectrum Ω I G n J)(hp:T.Reads p Z) {e:I→Support n}
    (hm:T.Costs p e t A) (hv:∀ i,s (f i)⊆e i)
local notation "S"=> mantra T f
noncomputable def proper_read (K:WayK Ω I G n): Source G n Ω (Whole V):= fun x i U=> sound (fun j:I=>glyph (f j)) (fun t s=> K x t s i U) -- deterministic
lemma page : (mantra T f).printP (proper_read f K)=Publishing.script (ℓ) K T:= by
 have hh(i:I): (ℓ) i=(ℓ) i:= rfl
 unfold Scribe.printP mantra Publishing.script; congr 1; funext x i U; change Poly.send _ _=((T.raw x i U:ℂ)) • zProd (Z:=ℓ) (T.tag i); rw [zProp f,MergeProof.Menu.sent,mul_one]
lemma regard (hv:∀ i,s (f i)⊆e i): Publishing.Syntax (ℓ) s e:= by
 let g:=fun i:I=> pack ({f i}:Finset V); let u:I→ℂ:=fun _=>1; apply Emissions.Syntax.for_radii (q:=g) (B':=u); exact ⟨fun i=> singleton_nonempty _, fun i v h=> (mem_singleton.mp h).symm ▸ hv i ⟩ -- Eq orientation? `h:v=f i`
include hm
lemma romance (c:Ray (Whole V))(ha:0≤c)(hC:∀ i,c (book f i) ≤ B): (mantra T f).Spend p c t (B*A) := by
 obtain ⟨f0,hf,h⟩:= hm.rent.majorize; have hz:0≤ B:=(ha _).trans (hC ∅); refine ⟨f0, ⟨fun i=>(hf i).1,fun x i u hu=>?_⟩,fun i=>?_⟩; exact Blush.pricingG ((hf i|>.2 x).1) ((hf i|>.2 x).2 u hu)
 refine budget_mono (budget_scale hz (h i)) (fun i'=>?_) (fun i'=>?_)
 · split; exact mul_nonneg (mul_nonneg (ha _) (hf _|>.1)) (Real.exp_nonneg _); rfl
 split; next hi=> dsimp only [mantra]; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC _) (hf _|>.1)) (Real.exp_nonneg _)
 next=> simp
-- edit include lists. Foots before.Card.
include hp hv hm
lemma seen : (mantra T f).Proper p s:=by
 obtain ⟨v,hV,hB⟩:= hm.rent.majorize; refine ⟨ hm.locations,fun x i=> ?_, fun i v' x U hq hi=> ?_, fun i he=> ?_,fun i x U he=>?_⟩
 · exact (ornate (hV i|>.2 x|>.1)) -- order
 · obtain ⟨j,hj,rfl⟩:= Finset.mem_map.mp hi; exact Finset.Subset.trans (hv j) (hm.owned i j hj)
 · have hi : T.tag i=∅:= Finset.card_eq_zero.mp ((Finset.card_map _).symm.trans (show ((T.tag i).map f).card=0 from (congr_arg (fun z:(Ψ).Mode=> z.val.card) he))) -- maybe card_map _
   intro x; unfold mantra; dsimp only; rw [hp.quiet _ hi]; funext U; exact Complex.ofReal_zero -- edit
 exact congr_arg Complex.ofReal (hp.constant i he x U)
-- interface.Real stationary.We.Record
omit hp hm hv
-- read branch.G.Texture
end Planet
end YM.Qlocal.Reckoner
