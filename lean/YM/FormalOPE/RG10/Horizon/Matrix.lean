import YM.FormalOPE.RG10.Horizon.Survey
/-! # A legitimate far-probe matrix with time-reflected test & fields in the other length's
renormalization. Inverse costs (see `rate`). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Apertures
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries

variable {G : Gauge} {F: Frames G} (R: Rails F){P:Plan F} {Y:Drivers} (Z:Patience P Y)
local notation "▵" s => Next.UVStress.dilate (Real.exp_pos (s))

lemma round (n:ℕ) (s:ℝ) (f:Test n): (▵ (-s)) ((▵ s) f)= f:= by -- parentheses
  ext1 x; change (↑((Real.exp (-s) ^ (4*n))⁻¹) : ℂ) *((↑((Real.exp s^(4*n))⁻¹):ℂ) * f (_⁻¹ • (_⁻¹ • x)))=f x
  have he:= Real.exp_pos s; rw [Real.exp_neg,inv_pow,inv_inv,inv_inv,inv_smul_smul₀ he.ne']; push_cast; field_simp

private lemma squared {I : Type*} [Fintype I]{S: Type*}[CommSemiring S]
    (f : Mark I Profile.n→S) (K:Matrix I I S) (T:Test 2)(i j : I):
    PertExtension.Position.insert I Profile.n f K ⟨⟨2,T⟩,![i,j]⟩ = (K * (Matrix.of fun a b:I=> f ⟨⟨2,T⟩,![a,b]⟩) * Kᵀ) i j := by
  let F (p:I × I) := f ⟨⟨2,T⟩,![p.1,p.2]⟩* (K i p.1*K j p.2)
  unfold PertExtension.Position.insert
  calc
    _ = ∑ p:I×I,F p:= Fintype.sum_equiv (finTwoArrowEquiv I) _ _ (fun x=>by
      change f ⟨⟨2,T⟩,x⟩*_ = f ⟨⟨2,T⟩,![x 0,x 1]⟩* _; congr 1
      · exact congr_arg (fun x=> f (⟨⟨2,T⟩,x⟩: Mark I Profile.n)) (by ext1 i; fin_cases i <;> rfl)
      change (∏ i':Fin 2,K (![i,j] i') (x i')) = _; simp [Fin.prod_univ_succ])
    _ = _:= by
      rw [Fintype.sum_prod_type]; simp only [Matrix.mul_apply,Matrix.transpose_apply, Matrix.of_apply,Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro i hi; unfold F; dsimp only; ring
namespace Halo
variable (B:Halo) (d:ℕ) (t:ℝ)
local notation "θ" => R.flow.warp
local notation "J" => Deck F d
local notation "M" => Matrix (Deck F d) (Deck F d)
local notation "T" => R.route d
abbrev qd {ι : Type*} (s:Test 2) (x y:ι) : Mark ι Profile.n:=⟨⟨2,s⟩,![x,y]⟩
def center : Matrix (Deck F d) (Deck F d) fps:= of fun i j=> R.adjust Z d (qd B.shape i j)
def look := B.center R Z d * (swing d upright)ᵀ.map PowerSeries.C
/-- Exterior label and reflected signs both at true orientation. -/
def external : Matrix (Deck F d) (Deck F d) fps:= R.drive (-t) d
private abbrev stampFace := (of fun i j:J=> R.adjust Z d (qd ((▵ t) B.shape) i j))
def Lens : Matrix (Deck F d) (Deck F d) fps := (stampFace R Z B d t * (external R d t)ᵀ) * (swing d upright)ᵀ.map PowerSeries.C
lemma secures (h: Valid F d B) : IsUnit (B.look R Z d).det:= by
 rw [PowerSeries.isUnit_iff_constantCoeff,RingHom.map_det]; apply isUnit_iff_ne_zero.mpr;
 suffices m: constantCoeff.mapMatrix (B.look R Z d) = Apertures.pane F d B from m ▸ h
 unfold look Apertures.pane; rw [map_mul]; congr 1
 · ext i j; change constantCoeff (R.adjust Z d _) = _; rw [Rails.inherits]; rfl
lemma face (h:Street Z R) : (stampFace R Z B d t).map (θ t)=R.drive t d * B.center R Z d * (R.drive t d)ᵀ := by
 ext i j:1; change θ t (R.adjust Z d (qd _ i j)) = _;
 rw [show (θ _) _ = _ from congr_fun (R.relocation (Z:=Z) h (a:=d) t) (qd ((▵ t) B.shape) i j)];
 erw [Position.move]; -- cod pull around actual Test
 change PertExtension.Position.insert J Profile.n (R.adjust Z d) (R.drive t d) (qd ((▵ (-t)) ((▵ t) B.shape)) i j)= _
 rw [round]; exact squared ..
lemma extern_inv : (external R d t).map (θ t)* R.drive t d=1 := by
 unfold external; rw [Grade.Rails.drive,Grade.Rails.drive, Passe.station_law,neg_add_cancel, Passe.station_base]
lemma invert (h:Street Z R) : (B.Lens R Z d t).map (θ t) = R.drive t d * (B.look R Z d) := by
 unfold Lens; rw [Matrix.map_mul,Matrix.map_mul,B.face R Z d t h];
 have hr: (((swing (F:=F) d upright)ᵀ).map C).map (θ t)= ((swing d upright)ᵀ).map C := by ext; simp [Flow.at_const]
 rw [hr, Matrix.transpose_map, Matrix.mul_assoc (R.drive t d * center R Z B d) (R.drive t d)ᵀ, ← Matrix.transpose_mul,extern_inv, transpose_one, Matrix.mul_one, Matrix.mul_assoc]; rfl
-- useful inverse formula before analytic
lemma launch (h:Street Z R): B.Lens R Z d t = (R.drive t d * B.look R Z d).map (θ (-t)):= by
 rw [← invert R Z _ d _ h]; ext i j:1; simpa only [Matrix.map_apply,neg_neg] using (R.ok.neutral (-t) (B.Lens R Z d t i j)).symm

def invertAt : Matrix (Deck F d) (Deck F d) Triangle.fps:= (B.look R Z d)⁻¹.map (θ (-t)) * external R d t
lemma left (h:Street Z R)(hb:Valid F d B) : B.invertAt R Z d t * B.Lens R Z d t=1:=by
 have he : external R d t * (R.drive t d).map (θ (-t))=1:= mul_eq_one_comm.mpr (by simpa only [external,neg_neg] using extern_inv R d (-t))
 rw [invertAt,launch R Z B d t h,Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (external R d t),he,one_mul, ← Matrix.map_mul,Matrix.nonsing_inv_mul _ (B.secures R Z d hb)]; simp
lemma right (h:Street Z R)(hb:Valid F d B) : B.Lens R Z d t*B.invertAt R Z d t=1:=mul_eq_one_comm.mp (B.left R Z d t h hb)
end Halo
end YM.FormalOPE.RG10.Apertures
