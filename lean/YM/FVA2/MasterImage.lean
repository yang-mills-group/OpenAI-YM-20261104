import YM.FVA2.PeriodicLines

/-!
# Undo the `b=true` image covariance, exactly. Now in real-space gauge semantics

No low-mode limit here. Image contributes `1+r`, where r reverses
incidence (there is *no* extra inversion factor in the stencil values).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Matrix Function Set Filter Finset Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian
open MS.Cylinder.Lab MS.Plane MS.Momentum MS.Book MS.Tone MS.Tone.Frame MS.City MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Fleet MS.Swirl MS.Swirl.Near MS.Cylinder.Taylor
open FVA2.Substitute FVA2.Ends FVA2.Lag FVA2.Letter
open Bloch (cell)
open scoped Classical
variable {G:Gauge} {n:Side}
local notation "F"=> Fourier G n
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "Ξ"=> iota G n
local notation "A"=> Words G n
local notation "I"=> FixedMode G n
local notation "e"=> brightness n
local notation "K"=> mat n (FinalK G)
set_option quotPrecheck false
local notation "Y0"=> (show Matrix I I ℂ from K)
local notation "U"=> χ G n
local notation "θ"=> label G n
local notation "C"=> periodicC G n
local notation "L"=> periodicL G n
local notation "R"=> symbolC G n
local notation "H"=> symbolL G n

def invX (i:X):X := (PertExtension.Orb.reflect i.1,i.2)
lemma inv_in : Involutive (invX (G:=G ) (n:=n)) := fun i=> by simp only [invX,PertExtension.Orb.reflect_reflect]

def reflectX (G:Gauge)(n:Side) : Matrix (X_ G n) (X_ G n) ℂ:= -Jfun invX
def reflectY (G:Gauge)(n:Side) : Matrix (Y_ G n) (Y_ G n) ℂ:= JY G n
local notation "r"=> reflectX G n
local notation "c"=> reflectY G n
local notation "W"=> moveL r r c c
lemma rX : r*r=1:= by unfold reflectX; rw [neg_mul_neg]; exact Jfun_square _ inv_in
lemma rY : c*c=1:= Jfun_square _ fy
lemma rsym : rᵀ=r := by unfold reflectX; rw [transpose_neg]; exact congr_arg Neg.neg (symmetryJ _ inv_in)
lemma csym : cᵀ=c:=symmetryJ _ fy

lemma cell_invShift (i:Axis)(x p:Site n) :
     cell (-x-step i) p=cell x (-p)* (mid (-Coord p) i)^2 := by
  have hx : Tone.bill (Coord p) (Tone.embed (step i))=cell (step i) p:= by rw [Tone.rights, ← wrap_step n]; exact (φ_c _ _).symm
  rw [Bloch.cell_sub, ← hx, Bloch.cell_duality (-x) p,Bloch.cell_inverse, Bloch.cell_duality p x, Bloch.cell_inverse,centr,rightadd,mid,opp,_root_.mul_inv_rev,pow_two] --

def unitN : Matrix I I ℂ:= Matrix.of fun i j=> if i=(Ξ).mode j then (Ξ).spin j else 0
lemma comesN : (show Matrix I I ℂ from Master G n true)=Y0+ (unitN (n:=n) (G:=G))*Y0:= by
  ext i j; change _+imageW _ _ _ _= K i j+((unitN (n:=n) (G:=G))*Y0) i j; rw [Matrix.mul_apply, image_u (riverOK BankK.pin BankK.gov)];
  rw [Finset.sum_eq_single_of_mem ((Ξ).mode i) (Finset.mem_univ _),unitN,of_apply, if_pos ((Ξ).perm i).symm,mul_comm ((Ξ).spin _)]
  intro b _ hb; unfold unitN; rw [of_apply,if_neg (fun he=>hb (by rw [he,(Ξ).perm])),zero_mul]
lemma comesN' : (show Matrix I I ℂ from Master G n true)= Y0+Y0*(unitN (n:=n) (G:=G))ᵀ:= by
  ext i j; change _+imageW _ _ _ _= K i j+(Y0*(unitN (n:=n) (G:=G))ᵀ) i j; rw [Matrix.mul_apply]; unfold imageW
  rw [Finset.sum_eq_single_of_mem ((Ξ).mode j) (Finset.mem_univ _),transpose_apply, unitN,of_apply, if_pos ((Ξ).perm j).symm]
  intro b _ hb; rw [transpose_apply,unitN, of_apply, if_neg (fun he=>hb (by rw [he,(Ξ).perm])), mul_zero]
lemma Ro_spin (p:Site n)(i:Axis)(b:Bool)(j:G.ColorIndex) :
    (Ξ).spin (((some i,b),j),p)= -mid (-Coord p) i ^2 := by change (-1:ℂ) * _ = _; rw [neg_mul, one_mul]; rfl
lemma Ro_none (p:Site n)(b:Bool)(j:G.ColorIndex) : (Ξ).spin (((none,b),j),p)=1:= by change 1 * (bill (-Coord p) 0)^2 = _; rw [right0,one_pow,one_mul]
lemma reverse_map : Uᵀ*F*unitN = W*(Uᵀ*F) := by
    rw [index_L]; ext i y; rw [Matrix.mul_apply, Matrix.mul_apply,Finset.sum_eq_single_of_mem ((Ξ).mode y) (Finset.mem_univ _),unitN,of_apply, if_pos rfl,sum_all]
    swap; · intro b _ hb; simp [unitN,hb]
    -- evaluate θ reversal
    rcases i with ⟨⟨x,i⟩,a⟩|⟨⟨x,i⟩,a⟩|⟨p,a⟩|⟨p,a⟩
    all_goals simp only [moveL, reflectX, reflectY,JY,Jfun,Matrix.neg_apply,of_apply,neg_mul,ite_mul,zero_mul,
       Finset.sum_const_zero,Finset.sum_neg_distrib,Finset.sum_ite_eq, add_zero,zero_add, submatrix_apply,
       id_eq,Finset.mem_univ,↓reduceIte,one_mul]
    all_goals
      rcases y with ⟨⟨⟨_|j,b⟩,y⟩,k⟩
    all_goals
      cases b <;> simp [invX, flip_pY, Fourier, label, iota_mode,Ro_spin,Ro_none,
        panel,panelIndex,Native.Paper,Native.Spectrum, Landau.leggin,Bonded.district,Focus.AId,
        Focus.KId,Landau.signA]
    case a.some.false | k.some.true =>
       simp only [PertExtension.Orb.reflect,cell_invShift]; split_ifs with he; rw [he.1]; rfl
    case c.none.false | b.none.true =>
       rw [Bloch.cell_duality (-p) k,Bloch.cell_inverse k, Bloch.cell_inverse, Bloch.cell_duality k p]

-- unprojected before Θ
lemma P_cover_grain : (Uᵀ*F)*Y0*(Uᵀ*F)ᵀ=grain C L:= by
  have he : Uᵀ*F=moveL (linksF G n) (linksF G n) (sitesF G n) (sitesF G n) * Uᵀ:= by rw [← F_rank,posMap,Matrix.mul_assoc (Uᵀ*F), leftM, Matrix.mul_one]
  simp_rw [he]; rw [transpose_mul,transpose_transpose]
  rw [ Matrix.mul_assoc (moveL _ _ _ _), ← Matrix.mul_assoc _ U, Matrix.mul_assoc (moveL _ _ _ _) (Uᵀ*Y0), chilled_all, commute_grain ]
lemma image_grain_R : (Uᵀ*F)*(show Matrix _ _ ℂ from Master G n true)*(Uᵀ*F)ᵀ = (show Matrix A A ℂ from grain C L) + W*(show Matrix A A ℂ from grain C L) := by
    rw [comesN, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc _ unitN, reverse_map, Matrix.mul_assoc W, Matrix.mul_assoc W,P_cover_grain]
lemma image_grain_L : (Uᵀ*F)*(show Matrix _ _ ℂ from Master G n true)*(Uᵀ*F)ᵀ = (show Matrix A A ℂ from grain C L) + (show Matrix A A ℂ from grain C L)*Wᵀ := by
    rw [comesN',Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (Uᵀ*F), Matrix.mul_assoc ((Uᵀ*F)*Y0) _ (Uᵀ*F)ᵀ,← transpose_mul _ unitN,reverse_map,transpose_mul W,← Matrix.mul_assoc _ _ Wᵀ,P_cover_grain]

abbrev MasterC (G:Gauge)(n:Side) := (1+reflectX G n)*periodicC G n
abbrev MasterL (G:Gauge)(n:Side) := (1+reflectY G n)*periodicL G n

lemma body_r (i j:X): (W*sigma C L) (Letter.a i) (Letter.a j)= (r*C) i j := by rw [Matrix.mul_apply,sum_all]; simp [sigma,moveL,Matrix.mul_apply]
lemma body_l (i j:X): (sigma C L*Wᵀ) (Letter.a i) (Letter.a j)= (C*r) i j := by
  rw [Matrix.mul_apply,sum_all]; conv_rhs => rw [← rsym]
  simp [sigma, moveL,Matrix.mul_apply]
lemma body_g (i:Y)(j:X): (W*sigma C L) (Letter.c i) (Letter.k j) = -(c*L) i j := by rw [Matrix.mul_apply,sum_all]; simp [sigma,moveL,Matrix.mul_apply, Finset.sum_neg_distrib]
lemma body_h (i:Y)(j:X): (sigma C L*Wᵀ) (Letter.c i) (Letter.k j)= -(L*r) i j := by
  rw [Matrix.mul_apply,sum_all]; conv_rhs => rw [← rsym]
  simp [sigma,moveL,Matrix.mul_apply,Finset.sum_neg_distrib]
lemma body_s (i:Y)(j:X): (W*sigma C L) (Letter.k j) (Letter.c i)=(L*r) i j:= by rw [Matrix.mul_apply,sum_all]; simp [sigma,moveL,Matrix.mul_apply] ; apply Finset.sum_congr rfl; intro x hx; rw [mul_comm]; exact congr_arg _ (show r j x=r x j from congr_fun (congr_fun rsym x) j)

lemma equal_mul : (W*sigma C L)=sigma C L*Wᵀ := by
    have ht:= add_left_cancel (image_grain_R (G:=G) (n:=n)|>.symm.trans image_grain_L)
    rw [sigma_half,Matrix.mul_smul,Matrix.smul_mul] at ht; exact (smul_right_injective _ (show (2:ℂ)⁻¹≠0 from by norm_num) ht) -- inspect
lemma rC_sync : r*C=C*r:= by ext i j; rw [← body_r,equal_mul,body_l]
lemma cL_sync : c*L=L*r:= by ext i j; apply neg_inj.mp; rw [← body_g,equal_mul,body_h]
lemma shape_Θ : (Uᵀ*F)*(show Matrix _ _ ℂ from Master G n true)*(Uᵀ*F)ᵀ= (show Matrix _ _ ℂ from grain (MasterC G n) (MasterL G n)):= by
  rw [image_grain_R, sigma_half,sigma_half,Matrix.mul_smul,← smul_add]; apply congr_arg ((2:ℂ)⁻¹ • ·)
  unfold MasterC MasterL; rw [Matrix.add_mul,Matrix.add_mul,Matrix.one_mul,Matrix.one_mul]; ext i j; rw [ Matrix.add_apply ]
  cases i <;> cases j
  case a.a => rw [body_r]; rfl
  case c.k=> rw [body_g]; simp [sigma]; abel
  case k.c=> rw [body_s,cL_sync]; rfl
  all_goals rw [Matrix.mul_apply, sum_all]; simp [sigma,moveL]
end YM.FVA2.Inversion
