import YangMills.WilsonProof.GraphOperands
import YM.FVA2.Position.Hall
import YM.FVA2.Arrival.Landing
import YM.XSpace.Output1
/-! # Through-size D frame on ACTUAL XSpace alphabet.

Same across all horizons; specialization to concrete Mesh here. Pre-substitute $g_*$ into bare
columns, carrying that order, then multiply $D^a$ on the actual on-shell alphabet, on right.
Entry in regulated length units includes ratio of two cutoff *engineering* powers. See
`Dframe/Bare` for the order-zero conclusion (stronger: **exact identity** at
every finite Mesh), and the real formal-frame assertion used for the position
comparison. Not claiming the positive-order entries converge as spacing tends to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes
open scoped Topology ContDiff BigOperators Classical
variable {n m d k:ℕ}{G:Gauge}{B:Deck G}
abbrev enroll (h:m≤k)(i: Glyph B m) : Glyph B k:= ⟨ ⟨ i.1.val,by have hi:=i.1.isLt; omega ⟩, i.2 ⟩
lemma size_le (i:Glyph B d): i.size ≤ d:= Nat.le_of_lt_succ (show i.1.val < d.succ from i.1.isLt)
local notation "Π"=> Press.portDeck G
lemma own_grade (i: Glyph B d): enroll (size_le i) (Land.read (panel i))=i:=rfl
local notation "M"=> Toon G
local notation "L"=> M d
abbrev theory (c: Toon G d): Sec G d:= Theater.Rune Π c
lemma theory_sig (c:Toon G d): (Daylight Π d) c=theory c:= readHeight ..
lemma real_sig (c:Toon G d): reel d (theory c)=theory c:= Subtype.ext (Theater.real_shell ..)
lemma lift_sig {l:ℕ}(h:d≤l) (c:L) : up h (theory c)=theory (enroll h c):=rfl
lemma include_sig (i:L): theory i= (up (size_le i)) (theory (read (panel i))):= rfl
lemma pure_sig (i:L) : en (size_le i) (Arrival.Birth.theory i)=theory i:= rfl
lemma yaw (i:L)(s:Signed) : ori s.ortho d (theory i)= rotateField s theory i:= by apply Subtype.ext; rw [rotateField, AddSubmonoidClass.coe_finsetSum]; exact letterSpin s i
lemma all_sig (p: Sec G d): (∑ c:Toon G d,(Daylight Π d).repr p c • theory c)=p:= by simp_rw [ ← theory_sig, Module.Basis.sum_repr ]

variable (ν:ℝ) (S:Prescription (Press.portDeck G)) (X:XSpace.Mesh)
abbrev ink (a:Toon G d)(b:Toon G a.size)(k:ℕ)(x:ℝ):ℝ:= ((S.fees a.size (panel a) k).register b).eval x
abbrev stake (u:Toon G d)(c:Toon G u.size)(k:ℕ): ℝ:= X.spacing⁻¹^ (u.size-c.size) * ink S u c k (ν-Arrival.Schedule.theta X)
def story (a:Toon G d)(k:ℕ): Sec G a.size:= ∑ c: Toon G a.size, stake ν S X a c k • theory c
def wold (d:ℕ)(k:ℕ): FieldEnd G d:= ( Daylight Π d ).constr ℂ (fun i=> up (size_le i) (story ν S X i k))
def D (d:ℕ) : Guard G d:= PowerSeries.mk (wold ν S X d)
lemma pays (d:ℕ)(k:ℕ): PowerSeries.coeff k (D ν S X d)= wold ν S X d k:= by rw [D,PowerSeries.coeff_mk]
lemma w_lit (i:L): wold ν S X d k (theory i)=up (size_le i) (story ν S X i k):= by rw [← theory_sig, wold,Module.Basis.constr_basis]
lemma longer (h:d≤k)(i:Glyph Π d): story ν S X ( enroll h i ) m=story ν S X i m:=rfl
lemma coast (p:Sec G d) (h:d≤k): wold ν S X k m (up h p)=up h ( wold ν S X d m p ):= by
 let A:= Daylight Π d; apply DFunLike.congr_fun ( f:=wold ν S X k m ∘ₗ up h ) ( g:=up h ∘ₗ wold ν S X d m ) (_ : _=_) p; apply A.ext; intro i; unfold A; rw [theory_sig]; simp only [LinearMap.comp_apply,w_lit,lift_sig,longer]; rfl
lemma preserves (p:Sec G d) (h:k≤d)(he:p.val∈ shellSector G k): ( wold ν S X d m p ).val∈ shellSector G k:= by
 let q:Sec G k:=⟨p.val,he⟩; rw [show p=up h q from rfl, coast]; exact ( wold ν S X k m q ).property
local notation "W"=> wold ν S X
-- summation.Proof.H
lemma stor_reel (i:Toon G d): reel i.size (story ν S X i k)=story ν S X i k := by unfold story; simp_rw [map_sum, reel_scale, real_sig]
lemma reel_up (p:Sec G k)(h:k≤d): reel d ( up h p ) = up h ( reel k p ):=rfl
lemma w_reel (p:Sec G d): reel d (wold ν S X d k p)=wold ν S X d k (reel d p):= by
 obtain he:= all_sig p; rw [ ← he ];
 simp only [map_sum, map_smul, (reel d).map_smulₛₗ,w_lit, reel_up, real_sig, stor_reel]

lemma up_yaw (p:Sec G k)(s:Signed)(h:k≤d): ori s.ortho d (up h p)=up h (ori s.ortho k p):=rfl
-- Signed-axis compatibility
lemma earn (a:L) (c:Toon G a.size)(s:Signed) (H:Favors.Horder S): (∑ i:Case G a.size a.grade, markS s G a.size a.grade a.2.2 i * stake ν S X (Axes.take a i) c k)= Favors.erect s (fun j:Toon G a.size=> stake ν S X a j k) c:= by
    have he:= congr_fun (H.property a.size (panel a) s k) c; let V:= ν-Arrival.Schedule.theta X
    have hp:(∑ i:Case G a.size a.grade, markS s G a.size a.grade a.2.2 i * ink S (Axes.take a i) c k V )= Favors.erect s (fun j:Toon G a.size=>ink S a j k V) c:= by
       unfold ink; replace he:= congr_arg (fun p:Polynomial ℝ=> p.eval V) he; simp only [Favors.move,Favors.erect, Finset.sum_apply,Pi.smul_apply,Polynomial.eval_finsetSum, Polynomial.eval_smul] at he; exact he
    let f:= X.spacing⁻¹ ^ (a.size - c.size); simp_rw [show ∀ j:Case G a.size a.grade, stake ν S X (Axes.take a j) c k= f * ink S (Axes.take a j) c k V from fun j=> rfl ]
    simp_rw [ mul_left_comm _ f (ink ..), ← Finset.mul_sum ]; rw [hp]; unfold Favors.erect; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> mul_left_comm f _ _
set_option maxRecDepth 4096 in
lemma stor_yaw (a:L)(s:Signed)(H:Favors.Horder S) : (∑ i:Case G a.size a.grade, markS s G a.size a.grade a.2.2 i • story ν S X (Axes.take a i) k)= ori s.ortho a.size ( story ν S X a k ):= by
    unfold story; simp_rw [ Finset.smul_sum, _root_.map_sum, show ∀ (j:ℝ) (u:Sec G a.size), ori s.ortho a.size (j • u)=j • ori s.ortho a.size u from fun j u=> map_smul ((ori s.ortho a.size).restrictScalars ℝ) j u, yaw, smul_smul]; -- F d implicit size definitional
    change (∑ x:Case G a.size a.grade,∑ i:Toon G a.size,(markS s G a.size a.grade a.2.2 x * stake ν S X (Axes.take a x) i k) • theory i)=_; rw [ Finset.sum_comm ]
    have he:= Favors.transpose s (fun i:Toon G a.size=> stake ν S X a i k) (fun i: Toon G a.size=> theory i) ( LinearMap.lsmul ℝ ( Sec G a.size )); refine Eq.trans ?_ he; refine Finset.sum_congr rfl (fun i _=>?_); change (∑ j:Case G a.size a.grade, _)= Favors.erect s (fun i:Toon G a.size=> stake ν S X a i k) i • theory i; rw [ ← earn ν S X a i s H, Finset.sum_smul]
lemma w_yaw (p:Sec G d)(s:Signed) (H:Favors.Horder S) : ori s.ortho d (wold ν S X d k p)= wold ν S X d k (ori s.ortho d p):= by
 let A:= Daylight Π d; apply DFunLike.congr_fun (f:=ori s.ortho d ∘ₗ W d k) (g:=W d k ∘ₗ ori s.ortho d) (_: _=_) p; apply A.ext; intro i; unfold A; simp_rw [theory_sig,LinearMap.comp_apply, w_lit, up_yaw, yaw, rotateField, map_sum, ← stor_yaw ν S X i s H ]; rw [_root_.map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); let j':= Axes.take i j; let z:= markS s G i.size i.grade i.2.2 j;
 change (up (size_le j')).restrictScalars ℝ (z • story ν S X j' k) = (W d k).restrictScalars ℝ (z • theory j'); simp only [ map_smul,LinearMap.restrictScalars_apply,w_lit ]
lemma w_unit0 (a:Toon G 0)(H:Ace.UnitP S) : W 0 k (theory a)= if k=0 then theory a else 0:= by
  rcases a with ⟨ ⟨i,hi⟩,j,h⟩; replace hi:i=0:=(by omega); subst i; let a:Toon G 0:=⟨ ⟨0,Nat.zero_lt_succ _⟩, j,h ⟩; rw [w_lit]; let y:= ν-Arrival.Schedule.theta X; change up _ (∑ c:Toon G 0, (X.spacing⁻¹ ^ (0-c.size) * Polynomial.eval y (( S.fees 0 (panel a) k ).register c)) • theory c)= _; rw [map_sum];
  simp_rw [ H.aq (panel a) k ]; simp_rw [Ace.register, (show Land.read (panel a)=a from rfl) ]; rw [Finset.sum_eq_single a];
  · simp only [  and_true, Nat.zero_sub,pow_zero, one_mul ]; split_ifs with ht <;> simp only [ Polynomial.eval_one, Polynomial.eval_zero, one_smul, zero_smul,map_zero ]; rfl
  · intro b _ h'; rw [ if_neg (fun ht=> h' ht.2), Polynomial.eval_zero,mul_zero, zero_smul,map_zero]
  simp
lemma w_unit (H: Ace.UnitP S) : W d k (leaf G d)= if k=0 then leaf G d else 0:= by
 let f:=up (Nat.zero_le d) (G:=G); let p:=leaf G 0; have h:leaf G d=f p:=rfl; rw [h,coast]; -- unfold f?
 split_ifs with hk
 · congr 1; rw [ ← all_sig p, map_sum ]; exact Finset.sum_congr rfl fun i _=> (map_smul ( W 0 k ) _ _).trans (congr_arg (_ • ·) ( (w_unit0 ν S X i H).trans (if_pos hk)))
 rw [ ← all_sig p,map_sum,Finset.sum_eq_zero (?_:∀ i∈_,(W 0 k) (_ • theory i)=0), map_zero ]; intro i _; rw [ _root_.map_smul,w_unit0 ν S X i H, if_neg hk, smul_zero ]
end YM.FVA2.Dframe
