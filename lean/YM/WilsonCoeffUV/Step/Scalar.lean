import YM.WilsonCoeffUV.Step.TorusPrecision

/-! Generic scalar/sums and restrictions. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators
variable {U V R:Type*}
abbrev Pal (R U:Type*) := ℕ → Gen R U
def flatPal (K : Matrix U U ℝ) : Pal ℝ U := fun i=> if i=0 then shine (orbQ K) else 0
def scrub [Zero R](P:Pal R U) : Pal R U := fun i=> if i=0 then 0 else P i
lemma restores (P:Pal ℝ U) (K:Matrix U U ℝ)(hp:P 0=shine (orbQ K)) : flatPal K + scrub P=P := by ext1 i; simp only [Pi.add_apply,flatPal,scrub]; split <;> rename_i h<;> simp [*]
lemma flat_count (K:Matrix U U ℝ) : shellK 2 (flatPal K) := by
  intro i j h; rw [flatPal]; split; next he => exact shine_dark (by omega)
  rfl
lemma flat_sym (K:Matrix U U ℝ)(he:K.transpose=K)(i:ℕ): Pure (flatPal K i) := by
  unfold flatPal; split; · exact shine_pure (orb_smooth K he)
  exact Pure.zero

-- implement scalar palette

def uband (u:PowerSeries ℝ) : Pal ℝ U := fun i=> shine (k:=0) (fun _=>coeff i u)

def lop (P:Pal ℝ U) : Pal ℝ U:= fun e r => if r=0 then 0 else P e r
lemma lop_pres (P:Pal ℝ U) : P=lop P+uband (mk (fun i=> P i 0 (fun j=> j.elim0))) := by
  ext e r i; by_cases h:r=0
  · subst r; simp only [Pi.add_apply,lop,uband, ↓reduceIte,Pi.zero_apply, zero_add,shine_lit,coeff_mk]; apply congrArg (P e 0); exact Subsingleton.elim ..
  simp [lop,uband,shine,h,Ne.symm h]

section finite
variable [Fintype U]
omit [Fintype U] in
lemma finite_shell {d}{P:Pal ℝ U}(h:shellK d P)(i) : FiniteGen (P i) := ⟨d+i+1,fun j hj=>h i j hj⟩
lemma flash_add {P Q:Pal ℝ U}(h:∀ i,FiniteGen (P i))(g:∀ i,FiniteGen (Q i)): flash (P+Q)=flash P+flash Q := by ext1 n; simp only [flash,coeff_mk,map_add]; exact visible_add (h n) (g n)
lemma flash_neg {P:Pal ℝ U}(h:∀ i,FiniteGen (P i)): flash (-P)= -flash P := by
  ext1 n; have hx:= visible_μ (h n) (-1); simp_rw [neg_smul,one_smul] at hx; simp only [flash, coeff_mk,map_neg]; exact hx
lemma flash_sub {P Q:Pal ℝ U}(h:∀ i,FiniteGen (P i))(g:∀ i,FiniteGen (Q i)): flash (P-Q)=flash P-flash Q := by
  rw [sub_eq_add_neg,flash_add h _,flash_neg g,sub_eq_add_neg];
  intro i; have hx := finite_μ (g i) (-1); rw [neg_smul,one_smul] at hx; exact hx
lemma flash_scrub (P:Pal ℝ U) (K:Matrix U U ℝ)(hp:P 0=shine (orbQ K)): flash P=orbC K+flash (scrub P) := by
  ext1 n; rw [map_add]; by_cases h:n=0
  · subst n; rw [flash,flash,coeff_mk,coeff_mk,hp,scrub,if_pos rfl, visible_shine,orbC]; simp [totalR]
  simp_rw [flash,orbC,coeff_mk,scrub,if_neg h,coeff_C, if_neg h,zero_add]
lemma flash_blank {P:Pal ℝ U}(h:P 0=0) : constantCoeff (flash P)=0 := by rw [←coeff_zero_eq_constantCoeff_apply,flash,coeff_mk,h]; simp [totalR]

def soil : PowerSeries ℝ →+* Ink U:=PowerSeries.map (MvPolynomial.C)
lemma uband_flash (u:PowerSeries ℝ): flash (uband (U:=U) u) = soil u := by ext1 n; rw [flash,coeff_mk,soil,coeff_map,uband,visible_shine,shell (fun _=>_) (fun j=> j.elim0)]
lemma flat_flash (K:Matrix U U ℝ): flash (flatPal K)=orbC K := by
  ext1 n; simp only [flash,flatPal,coeff_mk,orbC,coeff_C]; split_ifs; exact visible_shine _; simp [totalR]

variable [Fintype V] [DecidableEq U] [DecidableEq V]
omit [DecidableEq U] [DecidableEq V] in
lemma loom_finite (K:Matrix U V ℝ){P:Pal ℝ U} (h:∀ i,FiniteGen (P i)) : loom K (flash P)= flash (fun i=> fade K (P i)):= loom_fade K _ h

def plug : Matrix (U⊕V) V ℝ:= (rightFlag U V).transpose
omit [Fintype U] in
lemma plug_project : projectZero (U:=U) (Y:=V)=loom plug := by
  apply serial_ext (by simp [projectZero]) _ (by simp [projectZero,loom]); intro p
  have h (i:U⊕V): projectZero (path i)= loom plug (path i):= by
    rw [loom_pin]; unfold plug; cases i with
    | inl i=> rw [project_var]; simp [rightFlag]
    | inr i=> rw [project_ext,Finset.sum_eq_single i] <;> simp +contextual [rightFlag,@eq_comm _ i]
  induction p using MvPolynomial.induction_on with
  | C a=> rw [show C _=realS _ from rfl,loom_real]; simp [realS,projectZero,projectZeroPoly,MvPolynomial.algebraMap_eq]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p i q=> rw [map_mul C,map_mul,map_mul,show C (MvPolynomial.X i)=path i from rfl,h,q] -- expose path
omit [Fintype V] in
lemma fade_plug {r} [AddCommGroup R][Module ℝ R](P:Gen R (U⊕V))(x: Fin r → V) [Fintype V] : fade plug P r x=P r (Sum.inr ∘ x) := by
  classical
  rw [fade,Finset.sum_eq_single (Sum.inr ∘ x)]
  · simp [plug,rightFlag]
  · intro n _ hn
    obtain ⟨a,ha⟩ := Function.ne_iff.mp hn
    rw [Finset.prod_eq_zero (Finset.mem_univ a),zero_smul]
    change n a≠ .inr (x a) at ha; simp [plug,rightFlag,ha]
  simp
end finite
end YM.WilsonCoeffUV.Blue
