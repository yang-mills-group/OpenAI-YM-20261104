import YM.X.Scheme.Grade
/-!
Split zoom and parity action on Lie increments. Restriction on
filtration genuine (lower range). Unit always survives.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Function Filter Set Maxwell Maxwell.Free Pert.Position
open scoped Topology BigOperators Classical ComplexConjugate
variable {G : Gauge} (F : Labels.Frames G) {d e j : ℕ} (h : d ≤ e)
local notation "W" => (Model F)
local notation "U" => up F h
local notation "L" => Pert.Position.Buffer F

def sign (m:ℕ×ℕ):ℂ := (-1)^m.2
lemma sign_star {i:ℕ×ℕ}:star (sign i)=sign i:= by simp [sign]
lemma sign_mul : sign * sign=1:= by funext ⟨n,m⟩; simp only [sign,Pi.mul_apply,← mul_pow]; simp

def par (d:ℕ): Module.End ℂ (E F d):=scalePolDiff F sign d
@[simp] lemma par_up (p:E F d): par F e (U p)= U (par F d p) := (scalePol_up F sign h ..).symm
@[simp] lemma par_conj (p:E F d): (Model F).conj (hierarchy F).spin d (par F d p)=par F d ((Model F).conj (hierarchy F).spin d p):= scalePol_star F sign sign (fun _=>sign_star) .. -- notation dot?
@[simp] lemma par_signed (s:Signed)(p:E F d): Extra.FD.rideO F s.ortho d (par F d p)= par F d (Extra.FD.rideO F s.ortho d p):= scalePol_spin F sign ..
@[simp] lemma par_cycle (p:E F d): par F d (par F d p)=p:= (scalePol_mul ..).trans (by rw [sign_mul]; exact scalePol_one ..)
@[simp] lemma par_unit {d}: par F d ((Model F).unit d)= (Model F).unit d:= (scalePol_unit ..).trans (by simp [sign])
include h in
lemma par_lower {p:E F e}(hv:p∈lower F d e): par F e p∈ lower F d e:= by rw [up_pre F h] at hv ⊢; obtain ⟨q,rfl⟩:=hv; rw [par_up]; exact ⟨_,rfl⟩
def conjugator (B:L d): L d:=
  let b:=(par F d).restrictScalars ℝ |>.toContinuousLinearMap
  ⟨ b*B.val*b, by
     have he (v:E F d): (b*B.val*b) v=par F d (B.val (par F d v)):= rfl
     refine ⟨?_,?_,fun p=>?_,fun s p=>?_,fun p=>?_⟩
     · rw [he,par_unit,B.property.1,map_zero]
     · intro e h p hp; rw [he]; exact par_lower F h.le (B.property.2.1 e h _ (par_lower F h.le hp))
     · rw [he,he, ← par_conj,par_conj F (B.val _), B.property.2.2.1] -- proof_irrel needed
     · rw [he, he, ← par_signed,par_signed F s (B.val _),B.property.2.2.2.1]
     · rw [he,he,map_smul,B.property.2.2.2.2,map_smul] ⟩

lemma conjugator_eq (B:L d)(v:E F d) : (conjugator F B).val v=par F d (B.val (par F d v)):= rfl
def cPar : Module.End ℝ (L d) where
   toFun:=conjugator F
   map_add' x y := by
      ext1; ext1 v; rw [conjugator_eq]; change par F d (x.val (par F d v)+y.val (par F d v))=(conjugator F x).val v+(conjugator F y).val v; rw [map_add,conjugator_eq,conjugator_eq]
   map_smul' t x:= by ext1; ext1 v; rw [conjugator_eq]; change par F d (t • x.val (par F d v))=t • (conjugator F x).val v; rw [conjugator_eq,LinearMap.map_smul_of_tower]
lemma cPar_eq (B:L d)(p): (cPar F B).val p=par F d (B.val (par F d p)):= rfl
lemma cPar_cycle (B:L d) : cPar F (cPar F B)=B:= by ext1; ext1 p; simp only [cPar_eq,par_cycle]

def zoomL : L e →ₗ[ℝ] L d where
   toFun:=zoom F h
   map_add' x y:= by
      ext1; ext1 v; apply up_inj F h; change U _ = U (_+_); rw [map_add]; exact (zoom_eq F h _ _).trans (Eq.symm (congr_arg₂ _ (zoom_eq F h x v) (zoom_eq F h y v))) -- change maybe
   map_smul' z x:= by ext1; ext1 v; apply up_inj F h; change U _= U (z • (zoom F h x).val v); rw [LinearMap.map_smul_of_tower]; exact (zoom_eq F h _ _).trans (Eq.symm (congr_arg (z • ·) (zoom_eq F h x v)))
lemma zoomL_eq (x) (v:E F d) : U ((zoomL F h x).val v)= x.val (U v):= zoom_eq F h .. -- x.val dot issue?
lemma zoomL_mul (g:e≤j)(x:L j) : zoomL F h (zoomL F g x)=zoomL F (h.trans g) x:= by
   ext1; ext1 v; apply up_inj F (h.trans g); rw [zoomL_eq,← up_mul F h g, zoomL_eq, zoomL_eq,up_mul]
lemma zoomL_same {d}(x:L d): zoomL F le_rfl x=x:= by
   ext1; ext1 v; have hh := zoomL_eq F le_rfl x v; simpa only [up_same F,LinearMap.id_apply] using hh
lemma zoomL_par (x): zoomL F h (cPar F x)=cPar F (zoomL F h x):= by
   ext1; ext1 p; apply up_inj F h; rw [zoomL_eq,cPar_eq,cPar_eq,← par_up, zoomL_eq, ← par_up]

def hook (B:L d) : Module.End ℂ (E F e):= U ∘ₗ bufferL F B ∘ₗ cut F h ∘ₗ trim F d e
lemma hook_up (B:L d)(p:E F d): hook F h B (U p)= U (B.val p):= by change _ = U (bufferL F B p); simp only [hook,LinearMap.comp_apply,trim, ← scalePol_up,show scalePolDiff F (prune d) d p=p from trim_self F le_rfl _, up_cut]
lemma trim_star (p:E F e): trim F d e ((Model F).conj (hierarchy F).spin _ p)= (Model F).conj (hierarchy F).spin _ (trim F d e p):=(scalePol_star F _ _ (fun i=>by simp [prune]) p).symm

def hookB (B:L d) : L e:=
   ⟨ ((hook F h B).restrictScalars ℝ).toContinuousLinearMap, by
      refine ⟨?_,?_,fun p=> ?_,fun s p=> ?_,map_smul (hook F h B) _⟩
      · change hook F h B _ = _; rw [← up_unit F h,hook_up,B.property.1,map_zero]
      · intro j hj p hp; rw [up_pre F hj.le] at hp ⊢; obtain ⟨q,rfl⟩:=hp; change hook F h B _ ∈ _; by_cases ht:j≤d
        · rw [← up_mul F ht h, hook_up, ← zoomL_eq F ht]; exact ⟨_,(up_mul F ht h _).symm⟩
        · change U _∈_; exact ⟨_,up_mul F (le_of_not_ge ht) hj.le _⟩
      · let I (d:ℕ):=(Model F).conj (hierarchy F).spin d; obtain ⟨q,hq⟩ := (show trim F d e p∈LinearMap.range U by rw [←up_pre]; exact trim_lower F h p)
        change I e (hook F h B p)=hook F h B (I e p); unfold I hook; simp only [LinearMap.comp_apply]; rw [trim_star F, ←hq, up_conj, up_conj, up_cut, up_cut]; exact congr_arg _ (B.property.2.2.1 _)
      · let I (d:ℕ):=Extra.FD.rideO F s.ortho d; obtain ⟨q,hq⟩:= (show trim F d e p∈LinearMap.range U by rw [← up_pre]; exact trim_lower F h p)
        have ht : trim F d e (I e p)=I e (trim F d e p):=(scalePol_spin ..).symm
        change I e (hook F h B p)=hook F h B (I e p); unfold hook; simp only [LinearMap.comp_apply]; rw [ht, ← hq]; unfold I; rw [up_signed, up_signed, up_cut, up_cut]; exact congr_arg _ (B.property.2.2.2.1 s _) ⟩

def splitB : L d→ₗ[ℝ] L e where
   toFun:=hookB F h
   map_add' x y:= by ext1; ext1 p; change U (_+_)=_+_; rw [map_add]; rfl
   map_smul' z x:= by ext1; ext1 p; change U (z • _) = _; rw [LinearMap.map_smul_of_tower]; rfl
lemma splitB_up (x:L d)(v:E F d): (splitB F h x).val (U v)=U (x.val v) := hook_up F h x v
@[simp] lemma splitB_right (x:L d): zoomL F h (splitB F h x)=x:= by ext1; ext1 v; apply up_inj F h; rw [zoomL_eq,splitB_up]
end YM.PositionX
