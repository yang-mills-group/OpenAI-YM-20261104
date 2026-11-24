import YM.FVA2.FourierL

/-!
# Full periodic lines. Moore-Penrose laws in `priv` coordinates.

Not claiming normalized PT on the unsymmetrized space (harmonic obstruction).
Only after `imageV true` and inversion root will the acyclicity argument apply.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Matrix Function Set Filter Finset Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian
open MS.Cylinder.Lab MS.Plane MS.Momentum MS.Book MS.Tone MS.Tone.Frame MS.City MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Fleet MS.Swirl MS.Swirl.Near MS.Cylinder.Taylor
open FVA2.Substitute FVA2.Ends FVA2.Lag
open Bloch (cell)
open Complex (I)
open scoped Classical
variable {G:Gauge} {n:Side} {w:QP}
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "E"=> linksF G n
local notation "T"=> sitesF G n
local notation "e"=> brightness n
local notation "N"=> scaleZ n
local notation "S"=> symbolS G n
local notation "γ"=> symbolM G n
local notation "R"=> symbolC G n
local notation "H"=> symbolL G n
local notation "J"=> JX G n
local notation "K"=> JY G n
local notation "♯"=> Coord
local notation "φ"=> mid
local notation "ωp"=> wave
local notation "M"=> fullM G n

private lemma corner_mul {A B D: Type}[Fintype B][Fintype D][Fintype A][DecidableEq A]
    (F:A→ B→D→ℂ)(x:A)(h:∀ a:A,a≠x→∀ b c,F a b c=0) :
    (∑ i:A×B,∑ j:D,F i.1 i.2 j)=∑ b:B,∑ c:D,F x b c := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
  intro i _ hi; simp [h _ hi]

-- scaled contractions.
private lemma c_times (p: Site n) (i j:Axis) :
    (∑ k:Axis,(Landau.precision i k (ωp (♯ p)):ℂ)*(Landau.precision k j (ωp (♯ p)):ℂ))=
      ((ωp (♯ p)).sq:ℂ)* Landau.precision i j (ωp (♯ p)) := by exact_mod_cast Landau.k_times i j (ωp (♯ p))
private lemma sum_sq (p: Site n) : (∑ k:Axis,(ωp (♯ p) k:ℂ)*(ωp (♯ p) k:ℂ))=(ωp (♯ p)).sq:= by simp [Momentum.sq,pow_two]
private lemma sideways0 (w: Momentum Axis) (i:Axis) : ∑ k:Axis,(w k : ℂ)*Landau.precision i k w = 0 := by
    have he:(∑ k:Axis, w k * Landau.precision i k w)=0:= by
      unfold Landau.precision Landau.delta; simp_rw [mul_sub, Finset.sum_sub_distrib, mul_ite,mul_zero,Finset.sum_ite_eq, Finset.mem_univ, if_true,mul_left_comm _ (w i), ← Finset.mul_sum ]; simp [Momentum.sq,pow_two]
    exact_mod_cast he

private lemma halfU (i j:Axis)(x y: G.ColorIndex) (p r : Site n) :
    (R*S) ((p,i),x) ((r,j),y) = if r=p ∧ x=y then
    φ (♯ p) i * φ (-(♯ p)) j * ((Landau.precision i j (ωp (♯ p)) :ℂ)/ (ωp (♯ p)).sq) else 0:= by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, corner_mul (fun t k v=> R ((p,i),x) ((t,k),v) * S ((t,k),v) ((r,j),y)) (-p)]
  swap; · intro a ha b c; simp [moonesC,ha]
  simp_rw [moonesC,moonesS, true_and,ite_mul,zero_mul, Finset.sum_ite_eq,if_pos (Finset.mem_univ _)]
  split_ifs with he
  · let w:=ωp (♯ p); let Q:ℂ:=w.sq; let P (i j:Axis):ℂ:=Landau.precision i j w
    have ht(k:Axis) : (N * φ (♯ p) i * φ (-♯ p) k * P i k / Q^2) * (e * φ (♯ p) k * φ (-♯ p) j * P k j) =
      (φ (♯ p) i * φ (-♯ p) j / Q^2) * (P i k * P k j) := calc
      _ = (N*e)*(φ (♯ p) k * φ (-♯ p) k) * (φ (♯ p) i * φ (-♯ p) j / Q^2 * (P i k * P k j)):= by ring
      _ = _:= by rw [lightW,mid_inv]; simp
    dsimp only [Q,P,w] at ht; simp_rw [ht,← Finset.mul_sum,c_times]; by_cases h:p=0
    · rw [(mom_zero p).mpr h]; norm_num
    field_simp [not_congr (mom_zero p)|>.mpr h]
  simp
private lemma halfV (i j:Axis)(x y: G.ColorIndex) (p r: Site n) :
    (J*γ*H*J) ((p,i),x) ((r,j),y)= if r=p ∧ x=y then
    mid (♯ p) i * mid (-♯ p) j * ((ωp (♯ p) i:ℂ)*(ωp (♯ p) j:ℂ) / (ωp (♯ p)).sq)
    else 0:= by
    rw [Matrix.mul_assoc J γ H, rightJF _ fx, leftJF,submatrix_apply,id_eq,
      submatrix_apply,id_eq]; change (γ*H) ((-p,i),x) ((-r,j),y)=_
    rw [Matrix.mul_apply,Finset.sum_eq_single_of_mem (p,x) (Finset.mem_univ _),moonesM,moonesL]
    · simp only [and_self,if_true,neg_inj]; split
      · let w:=ωp (♯ p); let Q:ℂ:=w.sq
        rw [show e * _ * I * _ * (-N * _ * I * _ / _) = (N*e)*(-I^2)*(mid (♯ p) i*mid (-♯ p) j*((w i:ℂ)*(w j:ℂ)/ Q)) from (by dsimp [w,Q]; ring),lightW, Complex.I_sq, neg_neg, one_mul,one_mul]
      exact mul_zero _
    rintro ⟨t,v⟩ _ h
    rw [moonesM, if_neg (fun (hu:t=p∧x=v)=> h (Prod.ext hu.1 hu.2.symm)),zero_mul]

lemma SymbolGreen : R*S+J*γ*H*J=1-PX:= by
    ext ⟨⟨p,i⟩,x⟩ ⟨⟨r,j⟩,v⟩
    rw [Matrix.add_apply,halfU,halfV]; split_ifs with he
    · obtain ⟨rfl,rfl⟩:=he; by_cases hx:i=j
      · subst j; rw [mid_inv]; by_cases hp:r=0 <;> simp [PX,Landau.precision,
          Landau.delta, hp, ← add_div]
        · exact_mod_cast (mom_zero (0:Site n)).mpr rfl
        exact_mod_cast not_congr (mom_zero r)|>.mpr hp
      simp only [PX, Matrix.sub_apply,of_apply,Matrix.one_apply, hx, Prod.mk.injEq,and_false,false_and,
        ite_false, Landau.precision, Landau.delta]; push_cast; ring
    simp only [ Matrix.sub_apply,PX,Matrix.of_apply,Matrix.one_apply]; have hh : ((p,i),x)≠ ((r,j),v):=by rintro h; simp only [Prod.mk.injEq] at h; exact he ⟨h.1.1.symm,h.2⟩
    rw [if_neg hh,if_neg fun h=>hh h.1]; simp

lemma SymbolLeft : H*γ=1-PY:= by
    ext ⟨p,u⟩ ⟨r,v⟩; rw [mul_apply,Fintype.sum_prod_type,corner_mul (fun t k x=> H (p,u) ((t,k),x) * γ ((t,k),x) (r,v)) (-p) (by intro a ha b c; simp [moonesL,ha])]
    simp_rw [moonesL,moonesM,true_and,ite_mul,zero_mul, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    split_ifs with he
    · obtain ⟨hr,hu⟩:=he; subst r v; let w:= ωp (♯ p); let Q:ℂ:=w.sq
      have ht (k:Axis): -N*φ (-♯ p) k * I * (w k : ℂ)/ Q * (e * φ (♯ p) k * I * (w k:ℂ))= Q⁻¹*((w k:ℂ)*(w k:ℂ)):= by
         rw [show -N*φ (-♯ p) k * I * (w k : ℂ)/ Q * (e * φ (♯ p) k * I * (w k:ℂ))=(N*e)*(φ (♯ p) k * φ (-♯ p) k)*(-I^2)*(Q⁻¹*((w k:ℂ)*(w k:ℂ))) by ring, lightW,mid_inv,Complex.I_sq]; ring
      dsimp only [w,Q] at ht; simp_rw [ht, ← Finset.mul_sum,sum_sq]; by_cases hp:p=0
      · rw [(mom_zero p).mpr hp]; simp [PY,hp]
      rw [ inv_mul_cancel₀ (not_congr (mom_zero p)|>.mpr hp)]; simp [PY,hp]
    simp; simp only [PY, Matrix.one_apply,Matrix.of_apply]; have hh : (p,u) ≠ (r,v):= by rintro h; cases Prod.mk.inj h; grind
    simp [hh]

lemma SymbolCTrans : γᵀ*R=0:= by
    ext ⟨p,x⟩ ⟨⟨r,k⟩,v⟩
    rw [mul_apply, Matrix.zero_apply,Fintype.sum_prod_type,
        corner_mul (fun t a w=> γᵀ (p,x) ((t,a),w) * R ((t,a),w) ((r,k),v)) (-p)]
    swap
    · intro a ha b c; rw [transpose_apply,← neg_neg a,moonesM, if_neg (fun (h:_∧_)=> ha (by rw [h.1,neg_neg])),zero_mul]
    simp_rw [ transpose_apply,moonesM,true_and,ite_mul, zero_mul,
      Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]
    have he(t:Axis): R ((-p,t),x) ((r,k),v)=R ((r,k),v) ((-p,t),x):= by nth_rw 2 [← s_C]; rfl
    simp_rw [he,moonesC, neg_inj]; split_ifs with h
    · obtain ⟨hh,hh'⟩:=h; subst r; subst x
      let w:= ωp (♯ p); let Q:ℂ:=w.sq
      have ht (i:Axis): e*φ (♯ p) i*I*(w i:ℂ)*(N*φ (♯ p) k*φ (-♯ p) i*(Landau.precision k i w:ℂ)/Q^2)=
          (φ (♯ p) k*I/Q^2)*((w i:ℂ)*(Landau.precision k i w:ℂ)) := by
            rw [show e*φ (♯ p) i*I*(w i:ℂ)*(N*φ (♯ p) k*φ (-♯ p) i*(Landau.precision k i w:ℂ)/Q^2)=(N*e)*(φ (♯ p) i * φ (-♯ p) i)*((φ (♯ p) k*I/Q^2)*((w i:ℂ)*(Landau.precision k i w:ℂ))) from (by ring),mid_inv,lightW]; ring
      dsimp only [Q,w] at ht; simp_rw [ht,← Finset.mul_sum,sideways0,mul_zero]
    simp

lemma Lzero : (PY:Matrix Y Y ℂ)*H=0:= by
    ext ⟨p,i⟩ ⟨⟨r,j⟩,k⟩
    simp_rw [Matrix.mul_apply,PY, Matrix.of_apply]; by_cases h:p=0
    · simp [h,ite_mul]; subst p; rw [moonesL]; simp only [(mom_zero (0:Site n)).mpr rfl, div_zero, ite_self]
    simp [h]

-- longitudinal frame.
def seek : Matrix Y Y ℂ:= Matrix.diagonal (fun i:Y=> ((ωp (♯ i.1)).sq:ℂ)⁻¹)
lemma SymbolLong : e • (Hᵀ*K)= N • (J*γ*seek) := by
    ext ⟨⟨p,i⟩,u⟩ ⟨r,v⟩
    rw [Matrix.smul_apply,Matrix.smul_apply, seek,Matrix.mul_diagonal,rightJF _ fy,leftJF]; change e * H (-r,v) ((p,i),u) = N * (γ ((-p,i),u) (r,v) * _)
    -- use chill directly on (p,i),(-r,c); no fragile phase congr computations
    rw [moonesM]; by_cases he:r=p ∧ u=v
    · rw [if_pos he, he.1];
      change e * Chill (mat n (FinalK G)) (((some i,true),u),p) (((none,false),v),-p) = N*((_ * _ * _ * _) * ((ωp (♯ p)).sq:ℂ)⁻¹); rw [ChillK]
      change e * (N * ((φ (♯ p) i * Tone.bill (-♯ p) 0) * (if u=v then Complex.I*(↑(ωp (♯ p) i/(ωp (♯ p)).sq):ℂ) else 0 )))= _
      rw [if_pos he.2,right0]; push_cast; ring
    rw [if_neg he,moonesL,if_neg (fun (h:p= - -r∧v=u)=>he ⟨by rw [h.1,neg_neg],h.2.symm⟩)]; ring

-- positional forms
abbrev periodicC (G:Gauge)(n:Side) := linksF G n * symbolC G n * (linksF G n)ᵀ
abbrev periodicL (G:Gauge)(n:Side) := sitesF G n * symbolL G n * (linksF G n)ᵀ
local notation "Cx"=> periodicC G n
local notation "L"=> periodicL G n

lemma P_C : Cxᵀ=Cx := by unfold periodicC; rw [transpose_mul, transpose_transpose, transpose_mul,s_C,Matrix.mul_assoc]
lemma P_mom : L*M =1-HarmY := by
  have ht : L*M*T=(1-HarmY)*T := by
    rw [ Matrix.sub_mul,p_harmY, one_mul,periodicL]
    calc
      _ = T*(H*γ):= by unfold symbolM; simp only [Matrix.mul_assoc]
      _ = _ := by rw [SymbolLeft,Matrix.mul_sub,mul_one]
  have he:= congr_arg (· * (invT G n)) ht; change L*M*T * invT G n=(1-HarmY)*T*invT G n at he
  rwa [Matrix.mul_assoc (L*M), Matrix.mul_assoc (1-HarmY),invertT',mul_one,mul_one] at he

lemma P_range : (HarmY:Matrix Y Y ℂ) * L=0 := by unfold periodicL; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,p_harmY, Matrix.mul_assoc T, Lzero]; simp
lemma P_transverse : Mᵀ*Cx=0:= by
  have ht : Tᵀ*(Mᵀ*Cx)=0:= by
    unfold periodicC; rw [← Matrix.mul_assoc,← Matrix.mul_assoc, ← Matrix.mul_assoc, show Tᵀ*Mᵀ*E=γᵀ from Eq.symm (by unfold symbolM; rw [transpose_mul,transpose_mul,transpose_transpose,← Matrix.mul_assoc]), SymbolCTrans,Matrix.zero_mul]
  calc _ = ((invT G n)ᵀ*Tᵀ)*(Mᵀ*Cx) := by rw [← transpose_mul,invertT',transpose_one,Matrix.one_mul]
       _ = _:= by rw [Matrix.mul_assoc,ht,Matrix.mul_zero]
lemma gradrep : M*T=E*(N • (J * γ)) := by
  unfold symbolM
  have hi : E*(N • (J*Eᵀ))=1:= invertE'
  calc M*T= ( E*(N • (J*Eᵀ)) )*(M*T) := by rw [hi,Matrix.one_mul]
       _ = _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
lemma P_long : ∃ X':Matrix Y Y ℂ, Lᵀ=M*X':= by
  refine ⟨T*seek*invT G n,?_⟩
  have ht : Lᵀ*T=M*T*seek := by
    unfold periodicL; rw [transpose_mul,transpose_mul,transpose_transpose,gradrep,Matrix.mul_assoc E,Matrix.mul_assoc Hᵀ,squareT,Matrix.mul_smul,SymbolLong,Matrix.mul_assoc E,Matrix.smul_mul]
  calc _ = Lᵀ*T*invT G n := by rw [Matrix.mul_assoc,invertT',Matrix.mul_one]
       _ = _ := by rw [ht]; simp only [Matrix.mul_assoc]
lemma P_green : Cx*fullS G n+M*L=1-HarmX := by
  have hu : Cx*fullS G n*E=E*(R*S) := by unfold symbolS periodicC; simp only [Matrix.mul_assoc]
  have hv : M*L*E=E*(J*γ*H*J) := by
     unfold periodicL
     rw [Matrix.mul_assoc M _ _, ← Matrix.mul_assoc _ _ _, ← Matrix.mul_assoc, Matrix.mul_assoc _ Eᵀ, squareE , ← Matrix.mul_assoc, gradrep, Matrix.mul_smul, Matrix.mul_assoc E _ H, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm e N,lightW,one_smul,Matrix.mul_assoc]
  calc Cx*fullS G n+ M*L = (Cx*fullS G n+M*L)*E*invE G n:= by rw [Matrix.mul_assoc (_+_),invertE',mul_one]
       _ = _:= by
         rw [Matrix.add_mul, hu, hv, ← Matrix.mul_add, SymbolGreen, Matrix.mul_sub, ← p_harmX, mul_one]
         rw [show E-HarmX*E=(1-HarmX)*E by rw [Matrix.sub_mul,one_mul], Matrix.mul_assoc (1-HarmX),invertE',mul_one]

end YM.FVA2.Inversion
