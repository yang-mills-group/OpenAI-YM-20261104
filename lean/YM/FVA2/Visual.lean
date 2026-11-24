import YM.FVA2.LoomSpin
import YM.FVA2.TurnClock
/-!
# Coordinates on reads under H
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.FVA2.ColorCode
open Filter Topology Set Function
open Pert Pert.RawLabels Pert.Position PositionX Maxwell Maxwell.Free
open Lattice Labels MS MS.Local.Physical MS.Menus MS.Theater MS.Landau MS.Landau.Detect MS.SpinCode
open scoped Topology Classical ContDiff
variable {G:Gauge} (F:Frames G)
def datum {d:ℕ}(i:BasisIx G d): ℕ × ℕ:= (Glyph.size i,Glyph.grade i)
variable (s:Ortho)(d:ℕ)(i j:BasisIx G d)
local notation "Q"=> sameAxis F d
abbrev spin := Extra.FD.rideO F s d
def showsC := (Q).repr (spin F s d (Q i)) j
def shows := Complex.re (showsC F s d i j)
abbrev cargo (i: BasisIx G d) (c:Ortho):= spin F c d (Q i)
lemma displays : cargo F d i s= ∑ j:BasisIx G d, showsC F s d i j • Q j := ((sameAxis F d).sum_repr _).symm
lemma bar_s (p:E F d) : (Model F).conj (hierarchy F).spin d (spin F s d p)= spin F s d ((Model F).conj (hierarchy F).spin d p):= physical_inj F (by simp only [physical_real F,spin,physical_ortho F]; exact real_turn ..)
lemma held_real : ((shows F s d i j:ℝ):ℂ)= showsC F s d i j:= by
    let x:= Q i; let V:= spin F s d; apply Complex.conj_eq_iff_re.mp; change star _=_; let Y:=(Model F).conj (hierarchy F).spin d; have he : Y (cargo F d i s)=cargo F d i s:= by unfold Y cargo; rw [bar_s,conj_basisX]
    have hx : Y (cargo F d i s)= ∑ j:BasisIx G d, star (showsC F s d i j) • Q j:= by rw [ displays F, map_sum ]; simp [Y,conj_basisX]
    rw [he] at hx; unfold showsC; let K:=sameAxis F d; change star (K.coord j (cargo F d i s))= K.coord j (cargo F d i s); nth_rw 2 [hx]; rw [map_sum,Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]; rw [map_smul,show K.coord j ( (sameAxis F d) j)=1 from ?_,smul_eq_mul, mul_one ]; · rfl
    · simp [K]
    intro i h he; simp [K,he]
lemma turnedAt (x:E F d) {p}(h: physicalLabel F d x∈ Labels.Grade p): physicalLabel F d (spin F s d x)∈Labels.Grade p:= by
   rw [physical_ortho F s x]; have hp:= gradePart_mem p ( Labels.tensor s ((physicalLabel F d) x)); rwa [gradePart_turn, gradePart_self _ _ h] at hp
lemma fares {x:E F d} {p:ℕ×ℕ}(h:physicalLabel F d x∈ Labels.Grade p) (H: p ≠ datum j): (sameAxis F d).repr x j=0:= by
    let f (i:ℕ×ℕ):ℂ:= if i=p then 0 else 1; let C:= scalePolDiff F f d; have he {x:E F d} (i)(h:physicalLabel F d x∈Labels.Grade i): C x= f i • x:= physical_inj F (by rw [map_smul, show physicalLabel _ _ (C x)= _ from scalePol_physical F f x]; exact scalePol_pure F f _ h ); have hx:C x=0:= (he p h).trans (by simp [f]); let M:= Q -- good
    obtain h₀:= congr_arg (fun v:E F d=>M.coord j (C v)) (M.sum_repr x); rw [ map_sum,map_sum,hx,map_zero, Finset.sum_eq_single_of_mem j (Finset.mem_univ _) ] at h₀; · rw [map_smul, show C _= _ from he (datum j) (graded F j),show f (datum j)=1 from if_neg (Ne.symm H),one_smul,map_smul,show M.coord j (M j)=1 by simp, smul_eq_mul,mul_one] at h₀; exact h₀
    intro i _ h; rw [map_smul, show C _=_ from he (datum i) ( graded F i ), map_smul,map_smul,show M.coord j (M i)=0 by simp [h],smul_zero,smul_zero]
lemma shown_off (h:datum i≠datum j): showsC F s d i j=0:= fares F _ _ (turnedAt F s d (Q i) (graded F i)) h
-- linear extension to common.F

lemma forward_contract (t:Ortho): showsC F (s*t) d i j= ∑ k:BasisIx G d,showsC F t d i k*showsC F s d k j:= by
    change (Q).coord j (cargo F d i (s*t))= _; rw [show cargo F d i (s*t)= spin F s d (cargo F d i t) from physical_inj F (by simp [cargo,spin,physical_ortho]),displays F t, map_sum,map_sum ]; simp_rw [ map_smul ]; rfl
lemma white_count : showsC F 1 d i j= if i=j then 1 else 0:= by unfold showsC; rw [show spin F 1 d ( Q i ) = Q i from physical_inj F (by simp [spin,physical_ortho])]; simp [Finsupp.single_apply]
lemma shows_l (t:Ortho): shows F (s*t) d i j= ∑ k:BasisIx G d,shows F t d i k*shows F s d k j:= by apply Complex.ofReal_injective; simp only [ Complex.ofReal_mul, Complex.ofReal_sum,held_real ]; exact forward_contract ..
section owner
local notation "B"=> wings G
variable (p q: Land.Plaid (wings G) d)
lemma owner_exists (g :BasisIx G d)(h:g.size=d): ∃ y:Land.Plaid B d,g= Land.read y:= by
    rcases g with ⟨ ⟨i,hi⟩,x⟩; change i=d at h; subst d; exact ⟨ x,rfl⟩
lemma tag_survives {S:Type}[AddCommMonoid S](f : BasisIx G d→S)(h:∀ i, Glyph.size i≠ d→ f i=0) : ∑ i:BasisIx G d,f i = ∑ x:Land.Plaid (wings G) d, f (Land.read x):= by
    rw [Fintype.sum_sigma]; rw [Finset.sum_eq_single_of_mem (⟨d,Nat.lt_succ_self d⟩:Fin (d+1)) (Finset.mem_univ _)]; rfl
    intro i hi hx; refine Finset.sum_eq_zero fun j _=>?_; exact h _ (fun h=> hx (Fin.ext h))
abbrev fee (F:Frames G)(s:Ortho)(d:ℕ) (p q:Land.Plaid (wings G) d):= shows F s d (Land.read p) (Land.read q)
lemma owners : spin F s d (Q (Land.read p))=∑ q:Land.Plaid B d,(fee F s d p q:ℂ) • Q (Land.read q):= by
   change cargo F _ _ _= _; rw [displays]; simp_rw [fee, held_real]; exact tag_survives d _ (fun i hi=>by rw [shown_off,zero_smul]; exact fun h=> hi ((congr_arg Prod.fst h).symm))
lemma fare_l (t:Ortho): fee F (s*t) d p q=∑ r:Land.Plaid B d, fee F t d p r * fee F s d r q:= by
   unfold fee; rw [ shows_l, tag_survives d _ (fun i hi=> ?_) ]
   rw [ shows, shown_off ]; simp; exact fun h=> hi ((congr_arg Prod.fst h).symm)

abbrev letterOn {d:ℕ}(p:Land.Plaid (wings G) d): Label G d:= letter (Land.read p)
lemma arrow (t:Ortho): Labels.tensor t (letterOn p)=∑ q:Land.Plaid B d, (fee F t d p q:ℂ) • letterOn q := by
   have he:= congr_arg (physicalLabel F d) (owners F t d p); rw [map_sum] at he; simp_rw [ spin, physical_ortho, map_smul, physical_letter ] at he; exact he
end owner
open MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Book MS.Book.Convolve MS.Book.Program MS.Native MS.Native.Wilsonian
variable (T:Warehouse G)
def lobby (d:ℕ) : E T.F d →ₗ[ℂ] MS.Book.Convolve.T (Plate.Glow G):= (sameAxis T.F d).constr ℂ (fun i=> T.insertW i.size (letter i))
lemma elevator (i:BasisIx G d) : lobby T d (sameAxis T.F d i)= T.insertW i.size (letter i):= Module.Basis.constr_basis ..
lemma lobby_l (k:ℕ)(h:d≤k)(p:E T.F d): lobby T k (up T.F h p)=lobby T d p:= by apply LinearMap.congr_fun (f:=lobby T k ∘ₗ up T.F h); apply (sameAxis T.F d).ext; intro i; rw [LinearMap.comp_apply,same_up,elevator,elevator]; rfl
lemma foyer (i:Land.Plaid (wings G) d)(s:Signed) : lobby T d (spin T.F s.ortho d (sameAxis T.F d (Land.read i)))= Warehouse.markPose s (lobby T d (sameAxis T.F d (Land.read i))):= by rw [owners T.F s.ortho d i,map_sum,elevator,← T.whirl _ s]; simp_rw [map_smul,elevator]; exact Eq.symm (Eq.trans (congr_arg (T.insertW d) (arrow T.F d i s.ortho)) (by rw [map_sum]; simp_rw [map_smul]; rfl))
lemma lobby_h (p: E T.F d)(s:Signed): Warehouse.markPose s (lobby T d p)= lobby T d (spin T.F s.ortho d p):= by
   apply LinearMap.congr_fun (f:= Warehouse.markPose s ∘ₗ lobby T d) (g:=lobby T d ∘ₗ (spin T.F s.ortho d).toLinearMap); apply (sameAxis T.F d).ext; intro i; let h:=not_under i; let k:=i.size; let L₁:= Land.read (B:= wings G) (d:=k) i.2; let v:=sameAxis T.F k L₁; have ht:i=includeI _ h L₁:=rfl
   have he : sameAxis T.F d i=up T.F h v:= (same_up T.F h L₁).symm
   have hw:= foyer k T i.2 s; change Warehouse.markPose s (lobby T d _)= lobby T d (spin T.F s.ortho d _); rw [he,spin,up_signed,lobby_l,lobby_l]; exact hw.symm
lemma promise (i:BasisIx G d) (t:Team) (x:ℝ): Glyph.preambleM ( T.native (wings G) ) t i x = wobble G t x ( lobby T d (sameAxis T.F d i) ):= by rw [elevator, Glyph.preambleM, T.describes]; rfl
lemma purpose (t:Team) (s:Signed) (x:ℝ) (i:BasisIx G d) : Warehouse.markPose s (Glyph.preambleM (T.native (wings G)) t i x)= ∑ j:BasisIx G d,(shows T.F s.ortho d i j:ℂ) • Glyph.preambleM (T.native (wings G)) t j x := by simp_rw [promise,Warehouse.wobble_pose,lobby_h, show spin T.F _ _ _= _ from displays T.F s.ortho d i,map_sum,map_smul, held_real]
end YM.FVA2.ColorCode
