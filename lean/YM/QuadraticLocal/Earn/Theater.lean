import YM.QuadraticLocal.Earn.Wheels
/-!
 ## Reading, at each actual stencil and regulator.
 Visible peck kernels bundled together. Need all reading & movement within
 aperture-helmet.Mask.SC before checking culture budgets. This identity on
 TRUE Lamps supports uses unmasked formulas TIMELY at ALL stakeholders. The
 connected priced estimate may use additional normalization, stencils helmets etc.
 This supplies one of the identity pieces, not an exact correspondence
 between the projected analytic finite and infinite kernels on torus.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ ρ r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)
namespace Width
set_option quotPrecheck false
open Club Promote Press Accumulate
variable (S:Press X j)(B:Press.Receipt X S a e)(p: Press.Palette X q S C)
local notation "Z"=> Cable.links
local notation "L"=> q.count.val
local notation "Λ"=> (Accumulate.rootPrice X)
local notation "ω"=> Press.estate X C q S B
local notation "Q"=> (ω p ρ)
local notation "Θ"=> Press.plant X C q S
local notation "Θ'"=> Θ p
local notation "Ω"=> (Club.alliance X C)
local notation "F₀"=> Real.exp
local notation "Hℓ"=> (Width.stash ρ k)
local notation "V₁"=> (k:Finset ℕ) -- drop
local notation "Φ"=> (Club.reach X C q)
local notation "I"=> Accumulate.inside
local notation "Y"=> Press.Palette X q S C
local notation "Et"=> Fin (j+1)
local notation "Zℓ" t:max=> (S.news C t)
local notation "Qp"=> Press.placement X q S B ρ
local notation "K"=> Club.Keys X C
local notation "U" T:max=> Width.Viewer X S a T
variable {D T H :ℕ}
variable (U' : Width.Viewer X S a T)
local notation "A"=> (Club.alliance X C)
local notation "L₀"=> (Club.lowest X C)
local notation "V₀"=> (Club.site X C q)
local notation "z₀"=> (Club.roof X C q)
def fuelCuts (Lt:Side)(T H B R:ℕ):Prop:=
    B+1≤R ∧ H+T+1≤R ∧ T+2*Cable.links*(1+T/Lt.val)≤R -- name conflicts.L!
variable {b₀ R':ℕ}(hp:Width.fuelCuts q.count T H b₀ R')
local notation "S'"=> neighbors R' (z₀)
local notation "M!"=> (P.coarser q)
include B hp
set_option quotPrecheck false
lemma framing (hv: Width.Visible X C q S p U' H): (Q).region b₀ ⊆ neighbors R' (Club.roof X C q):=by
   rcases hv with ⟨hV,hS⟩; let u:= b₀
   unfold Row.region; split;
   next hh=> exact Corona.halo_mono hp.1 (Finset.Subset.refl _)
   next h=>
      let x:= Θ'; have hx:x.length ≤ T:= (mem_filter.mp hS).2.1; intro y hy; apply (neighbors_mem ..).2; rcases Finset.mem_union.mp hy with hy|hy
      · have he:(Q).atom.footprint (z₀)=bundle (z₀) x.atom.leg:= Paths.atom_foot _ x.atom -- name shadow
        change y∈(Q).atom.footprint z₀ at hy; rw [he] at hy; exact (Paths.where_slot (z₀) x.atom.leg y hy).trans ((show x.atom.length ≤ T from (Nat.le_add_left ..).trans hx).trans ((Nat.le_add_right ..).trans hp.2.2))
      obtain ⟨i,hi,h⟩:= mem_biUnion.mp hy; let K0:=(Q).binder; have hℓ:= Promote.oneVisit X C q x (Press.pinned X C q S B p) (p.snd.prop.1) i hi; refine (Paths.to_ball z₀ (K0.path i ++ (P.coarser q).wire i) h).trans ((K0.rate i).trans ((hℓ.trans ?_).trans hp.2.2))
      apply Nat.add_le_add hx; rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Cable.mass_mono q (hV.2 _ (Club.attends ..))) -- usable with T
-- even WITHOUT any lamps (from support earlier around root)
omit B in
lemma stations (hv: Width.Together X C q T H) (i:V)(hi:i∈ (Club.alliance X C).val) : (P.coarser q).support i ⊆ S':= by
   let p:=Club.joint X C i; let q':= Club.stamp X C p; let ℓ:=L; let P':=(X q'); have he:q'∈ C.val:=Club.attends ..; let w':= Club.mask X q q'; have hk:i∈ P'.mode.val:=Club.join_rank X C hi; intro y hy; obtain ⟨k,hk',rfl⟩:=mem_image.mp (show y∈(P.support i).image q.parent from hy); apply (neighbors_mem ..).2; apply (separation_triangle _ w' _).trans; apply (Nat.add_le_add ((Club.brings X C q q' he).trans hv.1) (?_ : separation w' (q.parent k)≤T+1)).trans ((Nat.add_assoc ..).symm.trans_le hp.2.1) -- tag b param incorrect
   apply Nat.le_of_mul_le_mul_left _ q.count.property; apply (Corona.foreshorten q P'.center k).trans; have hf : separation P'.center k≤ T:= (Binder.spread P'.binder P'.atom (Binder.covers P'.binder P'.atom i hk hk')).trans (hv.2 q' he); have he:=q.count.property; change _≤q.count.val*(T+1); rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_le_add_right (hf.trans (Nat.le_mul_of_pos_left T q.count.property)) _
omit hp B
local notation "π"=> Width.litList X C q S U'
-- finite grade selectors on each club

def Charges (i:Fin (j+1)): Finset (Press.Mint X q C (S.news C i)) := Finset.preimage (Width.litList X C q S U' i) Subtype.val Subtype.val_injective.injOn

lemma visits' (i:Fin (j+1))(k:Press.Mint X q C (S.news C i)): k∈ Width.Charges X C q S U' i ↔ k.val∈ Width.litList X C q S U' i:= Finset.mem_preimage

noncomputable def audience (H:ℕ): Finset (Press.Palette X q S C):= if Width.Together X C q T H then Finset.univ.sigma (Charges X C q S U') else ∅
lemma ticket : p∈ audience X C q S U' H ↔ Visible X C q S p U' H:= by
    unfold audience Visible; split; next hh=> simpa only [mem_sigma,mem_univ,true_and, hh] using visits' X C q S U' p.fst p.snd
    next h=> simp [h]
-- show visible roll sum. Factor.PAINT of all values at full capability
local notation "ν"=> Trace.offered L₀ V₀

def suite (Uₗ:Width.Viewer X S a T) (g:ℝ): Config G c→ ℝ := ∑ i:Fin (j+1),∑ k∈ litList X C q S Uₗ i, Trace.offered (Club.lowest X C) (Club.site X C q) ((S.news C i).leg k) g i.val
local notation "𝓤"=> suite X C q S U'
local notation "Φp" x:max=> (∏ i∈C.val,(X i).paint x)
variable (ρ) (x:α) (v:Config G c)
include B
lemma speaks (hh: Width.Together X C q T H) (he:0<g): (Φp x) * Complex.ofReal (Width.suite X C q S U' g v)= ∑ k∈ Width.audience X C q S U' H,(Press.estate X C q S B k ρ).nominal g x v := by
-- edit .Lit
 unfold Width.audience Width.suite; rw [if_pos hh,Finset.sum_sigma]; simp_rw [Finset.sum_apply,Press.offered _ C q _ _ _ ρ x g v he,Complex.ofReal_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl; intro i _; let V:=(S.news C i); let A0:= Charges X C q S U' i; let s:= litList X C q S U' i; let τ: Press.Mint X q C V→ V.Ty:= Subtype.val; let f(x':V.Ty):ℂ:= (Φp x)*↑(Trace.offered (Club.lowest X C) (Club.site X C q) (V.leg x') g i.val v); have he :A0.image τ ⊆ s:=by rw [show A0=s.preimage τ Subtype.val_injective.injOn from rfl,Finset.image_preimage]; apply Finset.filter_subset
 calc
   ∑ i∈s,f i=∑ i∈A0.image τ, f i := by
      symm; apply Finset.sum_subset he; intro i' hi hK; have hp' : (V.leg i').atom.magnitude ≤ 0 :=by
          by_contra! h; exact hK (Finset.mem_image.mpr ⟨(show Press.Mint X q C V from ⟨i',(Finset.mem_filter.mp hi).2.2,h⟩),Finset.mem_preimage.mpr hi,rfl⟩)
      unfold f; rw [Press.ranked X C q (i':=i.val) hp']; simp
   _ = _:= by rw [Finset.sum_image (fun i hi j hj=>?_ )]; exact fun h=>Subtype.val_injective h
end Width
end YM.QuadraticLocal.Earn
