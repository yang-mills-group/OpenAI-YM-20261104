import YM.FVA2.LinkSymbol

/-!
# Fourier support for links and sites. Counts harmonic point as one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Matrix Function Set Filter Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian
open MS.Cylinder.Lab MS.Plane MS.Momentum MS.Book MS.Tone MS.Tone.Frame MS.City MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Fleet MS.Swirl MS.Swirl.Near MS.Cylinder.Taylor
open FVA2.Substitute FVA2.Ends FVA2.Lag
open Bloch (cell)
open scoped Classical

variable {G:Gauge} {n:Side}
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "F"=> Fourier G n
local notation "E"=> linksF G n
local notation "T"=> sitesF G n
local notation "e"=> brightness n
local notation "N"=> scaleZ n
local notation "S"=> symbolS G n
local notation "γ"=> symbolM G n
local notation "R"=> symbolC G n
local notation "H"=> symbolL G n

def flip_pX (i:X): X:= ((-i.1.1,i.1.2),i.2)
def flip_pY (j:Y): Y:= (-j.1,j.2)
lemma fx (i:X): flip_pX (flip_pX i) = i := by simp [flip_pX]
lemma fy (i:Y): flip_pY (flip_pY i) = i := by simp [flip_pY]

def Jfun {A:Type} [DecidableEq A] (p:A→A): Matrix A A ℂ:= Matrix.of fun x y=> if p x=y then 1 else 0
lemma leftJF {A P : Type}[DecidableEq A][Fintype A](p:A→A)(M:Matrix A P ℂ):
    Jfun p*M=M.submatrix p id:= by ext i j; simp [Jfun, Matrix.mul_apply,ite_mul]
lemma rightJF {A P:Type}[DecidableEq A][Fintype A](p:A→A)(hpp : Involutive p)(M:Matrix P A ℂ):
    M*Jfun p= M.submatrix id p:= by
  ext i j; rw [Matrix.mul_apply,Finset.sum_eq_single_of_mem (p j) (Finset.mem_univ _)]
  · simp [Jfun,hpp j]
  intro c hc hh; unfold Jfun; rw [of_apply, if_neg (fun he=>hh ((hpp c).symm.trans (congr_arg _ he))),mul_zero]
lemma Jfun_square {A:Type}[DecidableEq A][Fintype A](p:A→A)(hpp : Involutive p) : Jfun p*Jfun p=1:= by rw [leftJF]; ext i j; simp [Jfun,hpp i,Matrix.one_apply]
lemma symmetryJ {A:Type}[DecidableEq A](p:A→A)(h : Involutive p) : (Jfun p)ᵀ = Jfun p := by
  ext i j; by_cases he:p j=i; · simp only [transpose_apply,Jfun,of_apply, ←he,h j,↓reduceIte];
  simp only [transpose_apply,Jfun,of_apply,if_neg he, if_neg (fun hj : p i=j=>he (by rw [←hj,h i]))]

abbrev JX (G:Gauge)(n:Side): Matrix (X_ G n) (X_ G n) ℂ:= Jfun flip_pX
abbrev JY (G:Gauge)(n:Side): Matrix (Y_ G n) (Y_ G n) ℂ:= Jfun flip_pY

local notation "J"=> JX G n
local notation "K"=> JY G n

lemma cell2 (p r:Site n): (∑ i:Site n,cell i p * cell i r)=if -p=r then brightness n else 0 := by
  simp_rw [show ∀ i:Site n,cell i p *cell i r=cell r i * (cell (-p) i)⁻¹ from fun i=> by rw [Bloch.cell_duality (-p) i,Bloch.cell_inverse,inv_inv,Bloch.cell_duality r i, mul_comm]]
  rw [Bloch.orthogonal]; simp [δW,eq_comm]
lemma squareE : Eᵀ*E=e • J := by
  ext ⟨⟨p,i⟩,u⟩ ⟨⟨r,j⟩,v⟩
  simp_rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases he:i=j ∧ u=v
  · obtain ⟨rfl,rfl⟩:=he; simp [linksF,Jfun,ite_and,ite_mul,JX,flip_pX,cell2]
  push Not at he
  by_cases hx:i=j
  · subst j; simp [linksF,JX,Jfun,ite_mul,flip_pX,ite_and,he rfl,Ne.symm (he rfl)]
  simp [linksF,Jfun,ite_mul,JX,flip_pX,ite_and,hx,Ne.symm hx]
lemma squareT : Tᵀ*T=e • K := by
  ext ⟨p,u⟩ ⟨r,v⟩; rw [Matrix.mul_apply,Fintype.sum_prod_type]
  by_cases he:u=v
  · subst v; simp [sitesF,Jfun,ite_mul,JY,flip_pY,cell2];
  simp [sitesF,Jfun,he,Ne.symm he,ite_mul,mul_ite,JY,flip_pY]

abbrev invE (G:Gauge)(n:Side) := scaleZ n • (JX G n*(linksF G n)ᵀ)
abbrev invT (G:Gauge)(n:Side) := scaleZ n • (JY G n*(sitesF G n)ᵀ)

lemma invertE : invE G n * E=1:= by unfold invE; rw [Matrix.smul_mul,Matrix.mul_assoc, squareE, Matrix.mul_smul, Jfun_square _ (hpp:=fx),smul_smul,lightW,one_smul]
lemma invertT : invT G n*T=1:= by unfold invT; rw [Matrix.smul_mul,Matrix.mul_assoc, squareT,Matrix.mul_smul,Jfun_square _ (hpp:=fy),smul_smul,lightW,one_smul]
lemma invertE' : E*invE G n=1:= mul_eq_one_comm.mp invertE
lemma invertT' : T*invT G n=1:= mul_eq_one_comm.mp invertT

-- actual omitted projectors

def PX : Matrix X X ℂ := Matrix.of fun i j=> if i=j∧ i.1.1=0 then 1 else 0
def PY : Matrix Y Y ℂ := Matrix.of fun i j=> if i=j∧ i.1=0 then 1 else 0

def HarmX : Matrix X X ℂ := Matrix.of fun i j=> if i.1.2=j.1.2 ∧ i.2=j.2 then N else 0
def HarmY : Matrix Y Y ℂ := Matrix.of fun i j=> if i.2=j.2 then N else 0
lemma cell0 (x: Site n) : (∑ i:Site n,cell i x)= if x=0 then e else 0:= by
  by_cases hx:x=0
  · subst x; simp [δW]
  simp_rw [show ∀ i:Site n, cell i x=cell x i from fun i=> Bloch.cell_duality i x,Bloch.sum_cell hx]; exact (if_neg hx).symm
lemma p_harmX : HarmX*E=E*PX := by
  ext ⟨⟨p,i⟩,u⟩ ⟨⟨q,j⟩,v⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single_of_mem («f»:=fun v':X=> E ((p,i),u) v' * PX v' ((q,j),v)) ((q,j),v) (Finset.mem_univ _)]
  · simp_rw [Fintype.sum_prod_type]; by_cases he:i=j
    · subst j; by_cases hu:u=v
      · subst v; simp [ite_and,ite_mul,linksF,PX,HarmX, ← Finset.mul_sum,cell0]; split; subst q; rw [δW]; simp; rfl
      simp [ite_and,ite_mul,linksF,PX,HarmX,hu,mul_ite]
    simp [ite_and,ite_mul,PX,linksF,HarmX,he]
  intro b _ hb; simp [PX,hb]
lemma p_harmY : HarmY*T=T*PY := by
  ext ⟨p,u⟩ ⟨q,v⟩; rw [Matrix.mul_apply,Matrix.mul_apply,Finset.sum_eq_single_of_mem («f»:=fun v':Y=> T (p,u) v' * PY v' (q,v)) (q,v) (Finset.mem_univ _)]
  · rw [Fintype.sum_prod_type]; by_cases hu:u=v
    · subst v; simp [ite_mul,mul_ite,HarmY,PY,sitesF,← Finset.mul_sum,cell0]; split; subst q; rw [δW]; simp; rfl
    simp [sitesF,HarmY,PY,ite_and,hu,ite_mul,mul_ite]
  intro b _ hb; simp [PY,hb]

lemma mom_zero (p : Site n) : ((wave (Coord p)).sq : ℂ)=0 ↔ p=0 := by
  refine ⟨ fun h=>?_, fun he=>?_⟩
  · have hk : wave (Coord p)=0:= NoWave _ (Complex.ofReal_injective h)
    by_contra hp; obtain ⟨i,hi⟩:= Bloch.step_picks p hp
    have hx (p:Site n) : Tone.bill (Coord p) (Tone.embed (step i))=cell p (step i):= by rw [← wrap_step n i,Tone.rights]; change be _ (Coord p)=_; rw [← φ_c]; exact Bloch.cell_duality ..
    obtain ht := triangle i (-Coord p); rw [neg_neg,hx,wave_neg, hk] at ht
    simp at ht; exact hi (sub_eq_zero.mp ht)
  subst p; simp [ξ_zero, Momentum.sq, wave,theta]

end YM.FVA2.Inversion
