import YM.Qlocal.Versal.Pavement
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c f C F: Side} {W₀:Burn.Locale G} {R:RG.Rep G f} {R':RG.Rep G F}
    {p p' : ℝ} {n b ℓ r k:ℕ}
-- ℓ capacity, one labelled copy per site, for either analytic ζ or further spends.
variable {X:Burn.Seed R W₀}
namespace Pad
variable (Z:Pad X k)
-- PAD from HasSlots or Forest.Temp (second case Aux reindexed only, not used to assert any step on actual vacuum).
section room
variable (V:Burn.Seed R W₀) (W: Finset ℕ) (hs: HasSlots R.p R.activities)
include hs
omit hs in
private lemma blank_keys (k:ℕ): Nonempty (Fin k) ∨ k=0:=by by_cases h:k=0; exact Or.inr h; exact .inl ⟨⟨0,Nat.pos_of_ne_zero h⟩⟩ -- not needed
open Set in
lemma settled (k:ℕ) : ∃ X:Pad V k, ∀ i,X.slip i∉ W:=by
 let v: Set ℕ:= W ∪ range (V.model)
 -- allocate infinitely many fillers to skip.H Data. Option params. Inject by anchor, stamp>> tag.GUI.
 let P:= Burn.spine (j:=f) R.p; let Q(i: Names f k)(n:ℕ):= blankRow f (P i.1, n*k+i.2.val)
 have hv:= W.finite_toSet.union (Set.finite_range V.model)
 have hp(i:Names f k)(x' n:ℕ)(hx:Q i x'=Q i n): x'=n:= by
    have h':k>0:=Nat.pos_of_ne_zero (fun H=> Fin.elim0 (H ▸ i.2)); have he:=congr_arg Prod.snd ((blankRow f).injective hx); change x'*k + i.2.val=n*k + i.2.val at he; rw [add_left_inj] at he; exact Nat.eq_of_mul_eq_mul_right h' he
 have hz(i:Names f k): ∃ n:ℕ,Q i n∉v:= by obtain ⟨n,hn⟩:= (hv.preimage (f:=Q i) ((show Injective (Q i) from fun _ _ H=> hp i _ _ H).injOn)).exists_notMem; exact ⟨n,hn⟩
 choose z hz using hz; have he : Injective (fun i:Names f k=> Q i (z i)):= by
    rintro ⟨i,j⟩ ⟨x,y⟩ H; have he:= (blankRow f).injective H; have hx:i=x:=congr_arg RegularAddress.site (congr_arg Prod.fst he); have hv:j.val=y.val:=by
       have hs:=congr_arg Prod.snd he; change z (i,j)*k+j.val=z (x,y)*k+y.val at hs; exact Eq.trans (by simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt] : j.val=(z (i,j)*k+j.val)%k) ((congr_arg (·%k) hs).trans (by simp [Nat.add_mod,Nat.mod_eq_of_lt y.isLt]))
    exact Prod.ext hx (Fin.ext hv)
 let f0 : Embedding (Names f k) ℕ:= ⟨_,he⟩
 exact ⟨⟨f0, (fun i=> by rw [hs.reg]; exact congr_arg Prod.fst (recorded (regularKeys f) (P i.1) (z i*k+i.2.val))),fun _=> hs.regular _,fun i hu=> hz i (Or.inr hu)⟩,fun i hn=>hz i (Or.inl hn)⟩ -- arity
end room
noncomputable abbrev zeroB (G:Gauge):Burn.Locale G:= fun _ _=>0
local notation "K"=> Burn.rise R (zeroB G)
noncomputable def labelUp (c:Side): ℕ ↪ ℕ:=⟨fun i=> (Burn.keys c).symm (.inr i),fun i j h=> Sum.inr_injective ((Burn.keys c).symm.injective h)⟩
local notation "L"=> labelUp f
section appear
lemma disjoint_b (i:ℕ) : L i∉ Set.range (Burn.pivot f):= by rintro ⟨p,h⟩; have hx: Burn.keys f (L i)=.inl p:= h ▸ rights ..; rw [show Burn.keys f (L i)=_ from (show _=.inr i from (Burn.keys f).apply_symm_apply _)] at hx; contradiction
lemma proceeds(i:ℕ) : (K).activities.reg (labelUp f i)=R.activities.reg i ∧ (K).activities.E (L i)=R.activities.E i:=by
 have hx: Burn.keys f (L i)=.inr i:=(Burn.keys f).apply_symm_apply _; simp only [Burn.rise,press,hx,Function.comp_apply, Sum.elim_inr, and_self]
lemma points(i: Site f): (K).activities.reg (Burn.pivot f i)= Burn.spine (j:=f) R.p i ∧ (K).activities.E (Burn.pivot f i)=0 := earns R.p R.activities (zeroB G) i
variable (V:Burn.Seed R W₀) (u:Pad V k) (ht:R.activities.Valid R.p p p')
local notation "Φ"=>Burn.pivot f
def night : Burn.Seed (Burn.rise R (zeroB G)) W₀:= {
   model:= V.model.trans L
   reg i := by change ((K).activities.reg (L (V.model i))).support= _ ∧ ((K).activities.reg (L (V.model i))).site= _; rw [(proceeds _).1]; exact V.reg i -- implicit inference
   value i := ((proceeds ..).2).trans (V.value _)
   off:= V.off }
private noncomputable abbrev tempo(x:Names f (k+1)): ℕ:= Fin.cases (Burn.pivot f x.1) (fun i=>labelUp f (u.slip (x.1,i))) x.2
set_option quotPrecheck false
local notation "Z"=> tempo V u
include u in
lemma financed : Nonempty (Pad (night V) (k+1)):= by
 have h(i j:Site f)(n:ℕ): Burn.pivot f i ≠ labelUp f n:= by intro hx; exact disjoint_b n ⟨i,hx⟩
 have hz: Injective (tempo V u):= by
    rintro ⟨i,p⟩ ⟨j,q⟩
    refine Fin.cases ?_ (fun a=>?_) p <;> refine Fin.cases ?_ (fun b=>?_) q <;> intro h'
    · exact Prod.ext ((Φ).injective h') rfl
    · exact False.elim (h i j _ h')
    · exact False.elim (h j i _ h'.symm)
    have hh:= u.slip.injective ((L).injective h'); exact Prod.ext (congr_arg (@Prod.fst (Site f) (Fin k)) hh) (congr_arg Fin.succ (congr_arg Prod.snd hh)) -- notation
 refine ⟨⟨⟨_,hz⟩,?_,?_,?_⟩⟩
 · rintro ⟨i,j⟩; refine Fin.cases ?_ (fun l=>?_) j; · exact (points ..).1
   exact ((proceeds ..).1).trans (u.ready _)
 · rintro ⟨i,j⟩; refine Fin.cases ?_ (fun l=>?_) j; · exact (points ..).2
   exact ((proceeds ..).2).trans (u.quiet _)
 · rintro ⟨i,j⟩; refine Fin.cases ?_ (fun l=>?_) j <;> rintro ⟨p,hp⟩; · exact h i p _ hp.symm
   exact u.fresh (i,_) ⟨p,(labelUp f).injective hp⟩
include ht
lemma honest : (Burn.rise R (zeroB G)).activities.Valid R.p p p':= by
 have hx(i:Site f): Fairness R.p i (court i R.p.B) (fun _:Config G f=>0) 0:= by
    have hu:= Fairness.enroll (u:=i) (X:= court i R.p.B) (p:=R.p) (G:=G) (f:=fun _ : ℕ=>0) (v:=fun _=>0) ∅ (by simp); simpa using! hu
 have hh:= Burn.remit R.p R.activities (zeroB G) ht hx (fun _ _ _ _=> rfl); simpa using! hh.1
lemma lately (x:Config G f): (Burn.rise R (zeroB G)).eval x=R.eval x:= by rw [Burn.point_reads _ _ x ht]; simp [zeroB,masked,Set.indicator]
omit ht
abbrev faded := ∀ i∉Set.range V.model, R.activities.E i=0
lemma serene (hq:faded V): faded (night V):= by
 intro i hi; by_cases hc:i∈ Set.range (Burn.pivot f); · obtain ⟨x,rfl⟩:=hc; exact (points ..).2
 rcases hL : Burn.keys f i with (x|x); · exact False.elim (hc ((Burn.rolled i).2 ⟨x,hL⟩))
 have he : i=labelUp f x:= (Burn.keys f).injective (hL.trans ((Burn.keys f).apply_symm_apply _).symm); refine he ▸ ((proceeds ..).2.trans (hq x ?_)); rintro ⟨z,h⟩; exact hi ⟨z, (congr_arg (labelUp f) h).trans he.symm⟩
end appear
end Pad
end YM.Qlocal.Versal
