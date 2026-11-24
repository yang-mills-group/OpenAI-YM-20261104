import YM.FVAAlt2.Home.Turn
/-! Operator rotation in the MS spelling. Projector real/physical tower
 *and* off shell literal Φ.G basis. Scaling conventions attested. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Finset Filter Lattice Labels Source Topology
open Extraction FormalOPE FormalOPE.RG10
open FormalOPE.RG10.Position (Plan Loft)
open Maxwell Extra.FD
open MS MS.Koszul MS.Theater MS.Menus MS.Local.Physical MS.Land MS.Lifting MS.Native MS.FVA MS.FVA.Motions MS.FVA.Town
open Matrix
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge} {L:Frames G} {B:Deck G}{b:Bool}{p: ℤ}{d k:ℕ}
local notation "λM"=> mast B d L
local notation "γ"=> Glyph B d
local notation:max "ρ" x:max i:max=> ride L (Signed.inclusionO x) i
variable (L) (s t:Signed)
-- spectrum operators.FTZ uses ride
abbrev stn (L:Frames G)(B:Deck G)(d:ℕ)(s:Signed) : Matrix (Glyph B d) (Glyph B d) ℂ:= Matrix.of (fun i j=> (mast B d L).repr (ride L (Signed.inclusionO s) d (mast B d L i)) j)
def stepR (L:Frames G)(B:Deck G)(d:ℕ)(s:Signed): Matrix (Glyph B d) (Glyph B d) ℝ:= (stn L B d s).map Complex.re
local notation:max "Θ" d:max s:max=> stn L B d s
local notation:max "T" d:max s:max=> stepR L B d s
lemma describes (i:Glyph B d) : ∑ j:Glyph B d,(Θ d s) i j • λM j=(ρ s d) (λM i):= λM|>.sum_repr _
lemma movesOn (i j:Glyph B d): (((T d s) i j:ℝ):ℂ)=(Θ d s) i j:= by
  refine clBasis λM ((freeTable L).conj (table_spin L) d) (@peg_bar G d L B) ?_ _; rw [Position.real_move,peg_bar] -- notation issues
lemma only_g (i j: Glyph B d)(h: ( i.size,i.grade )≠ (j.size,j.grade)): (Θ d s) i j=0:= metal_shell _ _ _ h (Loft.respected d (s:=s.ortho) _ ( pegFrame i )) -- args
lemma only_r (i j:Glyph B d)(h:(i.size,i.grade) ≠ (j.size,j.grade)): (T d s) i j=0:= Complex.ofReal_eq_zero.mp (by rw [movesOn,only_g _ _ _ _ h])
variable (B d) in
lemma θτ : Θ d s * (Θ d t) = Θ d ( t*s ):= by
 ext i j : 1; unfold stn; simp only [Matrix.mul_apply, Matrix.of_apply]; conv_rhs=> rw [map_mul, ← Position.moves,← describes L s i,map_sum,map_sum, Finsupp.finsetSum_apply]
 simp_rw [ map_smul,Finsupp.smul_apply]; rfl
variable (B d) in
lemma θ₁ : Θ d 1=1:= by ext i j : 1; unfold stn; simp only [Matrix.of_apply,map_one,Position.no_move, Module.Basis.repr_self]; by_cases h:i=j<;> simp [h,Matrix.one_apply]
lemma climb_eq (h:d≤k)(i j:Glyph B d) : (Θ k s) (up h i) (up h j)= (Θ d s) i j:= by
 unfold stn; let Ω n:= mast B n L; simp only [Matrix.of_apply]; conv_lhs=> rw [ show mast B k L (up h i) = _ from Eq.symm (up_one (L:=L) h i), Position.ride_high L h , show peg B i L=mast B d L i from rfl, ← describes L s i, map_sum, map_sum,Finsupp.finsetSum_apply]
 apply Eq.trans ( b:= ∑ x:Glyph B d, (Θ d s) i x • ((Ω k).repr ((Ω k) (up h x)) (up h j) ))
 · exact Finset.sum_congr rfl (fun y _=> by rw [map_smul,map_smul,Finsupp.smul_apply, show Position.higher L h ((mast B d L) y) = _ from up_one (L:=L) h y])
 simp only [ Module.Basis.repr_self, Finsupp.single_apply,(up_inj h).eq_iff,smul_eq_mul,mul_ite,mul_zero,mul_one ]; simp -- not rw describes? captures rhs with rw too
lemma climb_r (h:d≤k)(i j:Glyph B d): (T k s) (up h i) (up h j)=(T d s) i j:= congr_arg Complex.re (climb_eq L s h i j)

-- exact-height coordinates
abbrev localStep (L:Frames G) (B:Deck G) (d:ℕ) (s: Signed) : Matrix (Plaid B d) (Plaid B d) ℂ:= (stn L B d s).submatrix Land.read Land.read
variable (B d) in
lemma Ξ_roll : localStep L B d s * localStep L B d t= localStep L B d (t*s):= by
 ext i j : 1; change _= (Θ d (t*s)) (Land.read i) (Land.read j); rw [← θτ L B d s t,Matrix.mul_apply,Matrix.mul_apply]; let f:= fun x:Glyph B d=> (Θ d s) (Land.read i) x * (Θ d t) x ( Land.read j ); change ∑ k:Plaid B d, f (Land.read k)= ∑ k:Glyph B d, f k
 rw [← Finset.sum_image (f:=f)]; · apply sum_subset (Finset.subset_univ _); intro k _ he; unfold f; refine mul_eq_zero_of_left (only_g L s (Land.read i) k ?_) _; intro eq; apply he; have hk:= congr_arg Prod.fst eq; rcases k with ⟨⟨x,h⟩,j⟩; change d=x at hk; subst x; exact Finset.mem_image.mpr ⟨j,mem_univ _,rfl⟩
 exact fun i _ j _ h=> eq_of_heq (Sigma.mk.inj h).2
variable (B d) in
lemma step_id : localStep L B d 1=1:= by ext i j : 1; unfold localStep; rw [ θ₁ ]; by_cases h:i=j <;> simp [h,Matrix.one_apply,(show Injective ( Land.read (B:=B) (d:=d)) from fun i j ht=> eq_of_heq (Sigma.mk.inj ht).2).eq_iff] -- simp?
lemma toll (i: Plaid B d): ∑ j: Plaid B d, (Θ d s) ( Land.read i ) ( Land.read j ) • peg B (Land.read j) L=(ρ s d) (λM (Land.read i)):= by
 classical
 let f:= fun j: Glyph B d=> (Θ d s) ( Land.read i ) j • peg B j L
 change ∑ j: Plaid B d,f (Land.read j)=_; rw [ ← describes L s, ← Finset.sum_image (f:=f)]; rotate_left; · exact fun i _ j _ h=> eq_of_heq (Sigma.mk.inj h).2
 apply Finset.sum_subset (f:=f) (Finset.subset_univ _); intro j _ hj; unfold f; rw [ only_g L s _ _ (fun h=>?_ ),zero_smul ]; obtain ⟨⟨x,hx⟩,u⟩:=j; have h':d=x:= congr_arg Prod.fst h; subst x; exact hj (Finset.mem_image.mpr ⟨ u,mem_univ _,rfl⟩)
-- transport actual wires on this Plan. use B=seats, Loom.
open PertExtension.Orb.SlotEvaluation
variable {L}
variable (P:Plan L)
local notation "B₁"=> seats P.liftOff P.certified
local notation "V"=> Lobby.Table (Profiles.nativeR P) B₁
lemma mast_lifts (i:Plaid (seats P.liftOff P.certified) d) : P.liftOff.lift d (pegK (L:=L) ⟨d,i⟩)=announcedL ( Land.read i ):= loft_from P.liftOff P.certified i.2
lemma ribbon_l (i:Plaid (seats P.liftOff P.certified) d): Orient.pose s ∘ ((V).menu _ _ i.2) = ∑ j: Plaid (seats P.liftOff P.certified) d, localStep L B₁ d s i j • (V).menu _ _ j.2 := by
 let F:= (P.source d); let w:= weighted F (P.sound d) (P.chosen d); have hh (k: Plaid B₁ d) : (V).menu _ _ k.2=w ( P.liftOff.lift d (mast B₁ d L ( Land.read k )) ):= by rw [ show mast B₁ d _ _= _ from pegl k, mast_lifts ]; exact Eq.symm (funds (P.source d) (P.sound d) (P.chosen d) k.2)
 simp_rw [hh]; rw [ weight_s s F (P.sound d) (P.chosen d), P.certified.oriented , show s.ortho=Signed.inclusionO s from rfl,← toll L s i,map_sum,map_sum]; simp_rw [map_smul]; rfl
open MS.Plane MS.Plane.Wire MS.Landau MS.Landau.Detect MS.Tone MS.FVA.Town
lemma fit_R {J:Dot G Cover}{F:Law G}(h:Fits J F k p false): Fits (Orient.pose s J) (turnW G s F) k p false:=by
   unfold Fits; rw [poseXY,show turnW G s (Tone.run J) = MS.Arts.Pilot.beam (MS.Arts.flagS (m:=0) (Γx s) G) (Tone.run J) from rfl,← MS.Garment.beam_mask (MS.Arts.flagS (m:=0) (Γx s) G) (Tone.run J)]; intro x _; unfold fieldVal; let v:= s⁻¹
   let E:Law G:= MS.Book.mask k (Tone.run J)
   change Rest (fieldVal (turnW G s E) _) _ _
   have he(t:ℝ): fieldVal (turnW G s E) (ray x) t= MS.City.SideS s⁻¹ x * E ( sail (ray (x.map (permute s⁻¹))) t):= by unfold fieldVal; rw [certA, ← MS.High.ray_sail_sign ]; unfold MS.City.SideS; rw [ MS.High.sign_const ]
   rw [funext he, certA, ← MS.High.sign_dim s⁻¹ x]; exact Rest.smul _ (h (x.map (permute s⁻¹)) (fun x=> Bool.noConfusion x))
lemma fit_determines {J:Dot G Cover}{F H:Law G}(h:Fits J F k p false)(he:Fits J H k p false): F=H:=by
 funext i; obtain h:= h i (fun x=> Bool.noConfusion x); obtain ht:= he i (fun x=> Bool.noConfusion x); by_cases hx:p-fieldDim wfield i<0; rw [h.bottom hx,ht.bottom hx];
 have he:∃ v:ℕ,(v:ℤ)=p-fieldDim wfield i:= ⟨(p-fieldDim wfield i).toNat, Int.toNat_of_nonneg (by omega)⟩; obtain ⟨v,hv⟩:=he; exact ( (h.home v hv.le).trans ( if_pos hv ) ).symm.trans ((ht.home v hv.le).trans (if_pos hv))
lemma read_consist (i:Plaid (seats P.liftOff P.certified) d): turnW G s (Land.read i|>.read)=∑ j:Plaid (seats P.liftOff P.certified) d, localStep L B₁ d s i j • ( Land.read j|>.read ):=by
 let q:=V; have h:= fit_R s (q.rich d _ i.snd).ono; simp only [q] at h; obtain hr:= congr_fun (ribbon_l s P i) 0; rw [Finset.sum_apply] at hr; simp only [Function.comp_apply, Pi.smul_apply] at hr; rw [hr] at h; apply fit_determines h (Fits.sum _ fun j _=>?_ ); let T':= localStep L B₁ d s i j; by_cases he:(Land.read i).grade=(Land.read j).grade
 · simp_rw [show i.1.val=j.1.val from he]; exact Fits.smul _ ((V).rich d _ j.2).ono
 have ht:T'=0:= only_g L s _ _ fun ht=> he (congr_arg Prod.snd ht)
 unfold T' at ht; rw [ht,zero_smul,zero_smul]; exact Fits.zero _
end YM.FVAAlt2.Home

