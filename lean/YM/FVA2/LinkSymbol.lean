import YM.FVA2.Reletter

/-!
# Torus symbols using counting measure (unprojected for now)

The Fourier form of the quadratic part, derived from `labels_bulk` and the Hessian.
And the corresponding covariance (terminal of the true MS equation).
Keep negative-momentum signs in both. Phases of midpoints only on symbols.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Matrix Function Set Filter Finset Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian
open MS.Cylinder.Lab MS.Plane MS.Momentum MS.Book MS.Book.Convolve MS.Tone MS.Tone.Frame MS.City MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Fleet MS.Swirl MS.Swirl.Near MS.Cylinder.Taylor
open FVA2.Substitute FVA2.Ends FVA2.Lag FVA2.Letter
open Bloch (cell)
open scoped Classical

-- small jet rule (no Symm assumed, including odd slots)
lemma field_two {A B:Type} [Fintype A] (K: Matrix A B ℂ)(F:Raw A ℂ)(x y:B) :
    ξ[K] F [x,y]= (Kᵀ * Matrix.of (fun i j=> F [i,j])*K) x y := by
  rw [D_eval x (fieldChange _ _),field_D,Finset.sum_apply,mul_apply]
  simp_rw [Pi.smul_apply,D_eval y (fieldChange _ _),field_D,Finset.sum_apply,Pi.smul_apply,
    field_nil,at_D,smul_eq_mul, Finset.mul_sum, mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> by simp only [Matrix.of_apply,transpose_apply]; ring

variable {G:Gauge} {n:Side}
abbrev X_ (G:Gauge)(n:Side):=Z G (Edge (Site n))
abbrev Y_ (G:Gauge)(n:Side):=Z G (Site n)
local notation "θ"=> label G n
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "F"=> Fourier G n
local notation "C"=> χ G n

def posMap : Matrix (Words G n) (Words G n) ℂ:= Cᵀ*F*C

def linksF (G:Gauge)(n:Side) : Matrix (X_ G n) (X_ G n) ℂ:= Matrix.of fun i j=> if i.1.2=j.1.2∧ i.2=j.2 then cell i.1.1 j.1.1 else 0

def sitesF (G:Gauge)(n:Side) : Matrix (Y_ G n) (Y_ G n) ℂ:= Matrix.of fun i j=> if i.2=j.2 then cell i.1 j.1 else 0
local notation "E"=> linksF G n
local notation "T"=> sitesF G n

lemma F_rank : posMap=moveL E E T T:= by
  unfold posMap; rw [index_L,index_R]; ext i j
  rcases i with ⟨⟨x,i⟩,u⟩|⟨⟨x,i⟩,u⟩|⟨p,v⟩|⟨p,v⟩ <;>
    rcases j with ⟨⟨y,t⟩,w⟩|⟨⟨y,t⟩,w⟩|⟨q,z⟩|⟨q,z⟩
  all_goals simp [Fourier,linksF,sitesF, label, panel, panelIndex, Focus.AId, Focus.KId,
    Native.Paper, Native.Spectrum, Landau.leggin, Bonded.district, Landau.signA,moveL, eq_comm]

lemma Legged (P : Dot G Cover) : ξ[Cᵀ*F] (ξ[C] (docket n P)) = Bulk G n (sleeve lace (Tone.run P)):= by rw [comp_change,← Matrix.mul_assoc,leftM,one_mul,labels_bulk]
lemma T_wind : ξ[moveL E E T T] ((full n).total (priorFull G n) 0)= ξ[C] (flatH G n) := by
  rw [← F_rank,← read_total,posMap, ← comp_change]
  simp only [promised]; rw [Legged]

abbrev fullM (G:Gauge)(n:Side) := intoC ((full n).gradientGraph (G:=G))
abbrev fullS (G:Gauge)(n:Side) := intoC (costMatrix (priorFull G n))

def symbolM (G:Gauge)(n:Side) := (linksF G n)ᵀ * fullM G n * sitesF G n
def symbolS (G:Gauge)(n:Side) := (linksF G n)ᵀ * fullS G n * linksF G n
local notation "σ"=> symbolS G n
local notation "γ"=> symbolM G n
local notation "ϒ"=> Orbit.flag
lemma channels_M (i:X)(j:Y) : γ i j=flatH G n [θ (Letter.k i),θ (Letter.c j)]:= by
  obtain ht := total_hessian _ (prior_full_prop G n)
  have hx := congr_fun (T_wind (n:=n) (G:=G)) [Letter.k i, Letter.c j]; rw [field_two,field_two,index_L,index_R] at hx
  simp only [submatrix_apply,id_eq,Matrix.of_apply] at hx; rw [← hx]
  simp_rw [Matrix.mul_apply,sum_all, transpose_apply,moveL,Matrix.of_apply, zero_mul,mul_zero,Finset.sum_const_zero,add_zero, zero_add,ht.k_k ]; rfl
lemma channels_S (i j:X) : -σ i j=flatH G n [θ (Letter.a i),θ (Letter.a j)]:= by
  obtain ht:= total_hessian _ (prior_full_prop G n)
  have hx:= congr_fun (T_wind (n:=n) (G:=G)) [Letter.a i,Letter.a j]; rw [field_two,field_two,index_L,index_R] at hx
  simp only [submatrix_apply,id_eq,Matrix.of_apply] at hx; rw [← hx]
  simp_rw [ Matrix.mul_apply,sum_all, transpose_apply,moveL,Matrix.of_apply, zero_mul,mul_zero,Finset.sum_const_zero,add_zero,ht.a_a ]; unfold symbolS; simp only [ Matrix.mul_apply, transpose_apply,mul_neg, Finset.sum_neg_distrib,neg_mul]; rfl
variable (i j:Axis) (u v: G.ColorIndex) (p q:Site n)
local notation "D"=> Coord p
local notation "e"=> brightness n
local notation "n0"=> scaleZ n
local notation "wκ"=> wave (Coord p)

def mid (p:QP) (i:Axis) := Tone.bill p (Tone.Frame.z i)
lemma mid_inv : mid D i * mid (-D) i = 1:=by unfold mid; rw [opp]; exact mul_inv_cancel₀ (Tone.nonz _ _)
lemma moonesS : σ ((-p,i),u) ((q,j),v) =
      if q=p ∧ u=v then e * mid D i * mid (-D) j * (Landau.precision i j wκ : ℂ) else 0:= by
  by_cases he:q=p
  · subst q; apply neg_inj.mp; rw [channels_S]; change flatH G n [(((some i,false),u),-p),(((some j,false),v),p)] = _
    rw [Neg_S,Near.oriented]; simp only [true_and]; change _ * ((_ * _) * (if u=v then _ else 0))= _
    split
    · change e * ((ϒ _ (-(-D)) * ϒ _ (-D)) * (-(Landau.precision i j wκ : ℂ)))=_; rw [neg_neg]
      change e *((mid D i *mid (-D) j)*_)=_; ring
    simp
  rw [if_neg (fun h=> he h.1)]; apply neg_inj.mp; rw [channels_S, neg_zero]; exact S_hold _ _ p q he
lemma moonesM : γ ((-p,i),u) (q,v)=
      if q=p ∧ u=v then e * mid D i * Complex.I * wκ i else 0:= by
  by_cases he:q=p
  · subst q; rw [channels_M]; change flatH G n [(((some i,true),u),-p),(((none,false),v),p)] = _
    rw [Neg_S,Near.oriented]; simp only [true_and]
    change _ * ((_ * _) * (if u=v then _ else 0))=_
    split
    · change e * ((ϒ _ (-(-D)) * bill (-D) 0)*(Complex.I * (wκ i:ℂ)))=_; rw [neg_neg,right0,mul_one]; change e*(mid _ _*(Complex.I*(wκ i:ℂ)))=_; ring
    simp
  rw [if_neg (fun h=> he h.1), channels_M]; exact S_hold _ _ p q he

-- momentum Chill data by sectors.
def symbolC (G:Gauge)(n:Side) : Matrix (X_ G n) (X_ G n) ℂ := Matrix.of fun i j=> Chill (mat n (FinalK G)) (label G n (Letter.a i)) (label G n (Letter.a j))
def symbolL (G:Gauge)(n:Side) : Matrix (Y_ G n) (X_ G n) ℂ := Matrix.of fun i j => Chill (mat n (FinalK G)) (label G n (Letter.k j)) (label G n (Letter.c i))
local notation "R"=> symbolC G n
local notation "H"=> symbolL G n
lemma ε_sym (a b : Words G n) : Chill (mat n (FinalK G)) (θ a) (θ b) = (Koszul.cross a.p b.p : ℂ)*Chill (mat n (FinalK G)) (θ b) (θ a) := by
  unfold Chill; rw [stampL BankK.pin BankK.t, label_compatible,label_compatible]; ring
lemma s_C : Rᵀ=R := by
  ext i j; exact (ε_sym (Letter.a j) (Letter.a i)).trans (one_mul _)
lemma moonesC : R ((p,i),u) ((q,j),v)= if q= -p ∧ u=v then
    n0 * mid D i * mid (-D) j * (Landau.precision i j wκ:ℂ)/ ((wκ).sq:ℂ)^2 else 0:= by
  by_cases he:q= -p
  · subst q; change Chill (mat n (FinalK G)) (((some i,false),u),p) (((some j,false),v),-p)= _
    rw [ChillK]; simp only [true_and]
    change n0 * ((mid D i * mid (-D) j)*(if u=v then ↑(Landau.precision i j wκ/(wκ).sq^2) else 0)) =_; split; push_cast; ring; simp only [mul_zero]
  rw [if_neg (fun h=> he h.1)]; exact chillOff _ _ p q he
lemma moonesL : H (p,u) ((q,j),v)= if q= -p ∧ u=v then
    -n0 * mid (-D) j * Complex.I * (wκ j:ℂ)/((wκ).sq:ℂ) else 0:= by
  by_cases he:q= -p
  · subst q; unfold symbolL; rw [Matrix.of_apply, ε_sym]; change (-1:ℂ)* Chill (mat n (FinalK G)) (((none,false),u),p) (((some j,true),v),-p)= _
    rw [ChillK]; change -1*(n0 * ((bill D 0*mid (-D) j)*(if u=v then Complex.I*↑(wκ j/(wκ).sq) else 0)))= _
    rw [right0]; simp only [true_and]; split; push_cast; ring; simp only [mul_zero]
  rw [if_neg (fun h=> he h.1)]; unfold symbolL; rw [Matrix.of_apply, ε_sym, show Chill (mat n (FinalK G)) (θ (Letter.c (p,u))) (θ (Letter.k ((q,j),v)))=0 from chillOff _ _ p q he, mul_zero]

lemma chilled_all : Cᵀ*(show Matrix _ _ ℂ from mat n (FinalK G))*C=grain R H := by
  rw [index_L,index_R]; ext i j; rw [submatrix_apply,id_eq,submatrix_apply,id_eq]; unfold Letter.grain
  apply mul_left_cancel₀ (show (2:ℂ)≠0 from by norm_num)
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num)]
  change Chill (mat n (FinalK G)) (θ i) (θ j)= _; rcases i with i|i|i|i <;> rcases j with j|j|j|j 
  case a.a => rfl
  case k.c => rfl
  case c.k => rw [ε_sym]; change (-1:ℂ)* H i j= - _; simp
  all_goals
    change Chill _ _ _=0; unfold Chill mat; split <;> simp [EdgeV, FinalK,Bass, label, panel,panelIndex,
      Native.Paper, Native.Spectrum, Landau.leggin, Bonded.district, Focus.AId, Focus.KId, Landau.signA,Tail, Landau.choir]

end YM.FVA2.Inversion
